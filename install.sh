#!/usr/bin/env bash
# BurgerOS — загрузчик установки (BX-10).
#
# Короткий и неизменный по устройству: всё, что сложно, делает установщик из
# подписанного выпуска. Загрузчик только:
#   1. спрашивает лицензионный блок, домен и почту (или берёт их из ключей);
#   2. проверяет подпись блока своей цепочкой ключей;
#   3. забирает с GitHub подписанный список выпусков и выбирает версию;
#   4. проверяет подпись описания выпуска и отпечаток каждого файла;
#   5. кладёт Bun, сверив его отпечаток, и передаёт работу установщику выпуска.
# Доверие держится на подписи, а не на дороге: GitHub, зеркала и пакет
# выпуска от владельца проверяются одинаково.
#
# Нужны python3 и openssl 3 — они есть в Ubuntu 24.04 и 26.04.
set -euo pipefail
if ! command -v python3 >/dev/null 2>&1; then
  echo "Нужен python3 (он есть в Ubuntu 24.04). Установка остановлена, ничего не изменено." >&2
  exit 1
fi
self="$(readlink -f "$0")"
exec python3 -c 'import sys; src = open(sys.argv[1], encoding="utf-8").read(); exec(compile(src.split("\n#__BURGEROS_PYTHON__\n", 1)[1], sys.argv[1], "exec"))' "$self" "$@"
#__BURGEROS_PYTHON__
import base64
import functools
import hashlib
import io
import ipaddress
import json
import socket
import time
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import termios
import urllib.request
import zipfile

# Цепочка ключей подписи коробки (BX-7): первый ключ и звенья «новый ключ,
# подписанный предыдущим». Её подставляет команда выпуска владельца.
KEYCHAIN = json.loads(r'''{"root":"-----BEGIN PUBLIC KEY-----\nMCowBQYDK2VwAyEA13aixA9De5utIGqPUq/ihNeLK6CReZK6G4r7GIUlR7c=\n-----END PUBLIC KEY-----\n","links":[]}''')

LICENSE_PREFIX = 'BURGEROS-LICENSE-1:'
MANIFEST_CORE = 1
LIST_CORE = 1

# Коды выхода — часть неизменного стыка загрузчика с выпуском (BX-12).
EXIT_REFUSED = 2      # проверка не прошла или не хватает ответов

ROOT = os.environ.get('BURGEROS_ROOT', '/')


def path(*parts):
    return os.path.join(ROOT, *[part.lstrip('/') for part in parts])


SHARED = path('/opt/burgeros/shared')
STATE = path('/var/lib/burgeros')


class Refused(Exception):
    pass


def say(text):
    print(text, flush=True)


# ---------- ключи командной строки ----------

def parse_args(argv):
    options = {'mode': 'install', 'restore': None, 'continue': False, 'no_chain': False,
               'license_file': None, 'domain': None, 'email': None, 'from_file': None,
               'stand': False, 'explain_select': None, 'installed': None}
    flags = {'--continue': 'continue', '--no-chain': 'no_chain', '--stand': 'stand'}
    values = {'--license-file': 'license_file', '--domain': 'domain', '--email': 'email',
              '--from-file': 'from_file', '--installed': 'installed'}
    index = 0
    while index < len(argv):
        arg = argv[index]
        if arg in flags:
            options[flags[arg]] = True
        elif arg in values:
            if index + 1 >= len(argv):
                raise Refused(f'После {arg} нужно значение')
            options[values[arg]] = argv[index + 1]
            index += 1
        elif arg == '--restore':
            options['mode'] = 'restore'
            if index + 1 < len(argv) and not argv[index + 1].startswith('--'):
                options['restore'] = argv[index + 1]
                index += 1
        elif arg == '--update':
            options['mode'] = 'update'
        elif arg == '--print-hash':
            options['mode'] = 'print-hash'
        elif arg == '--explain-select':
            # Диагностика: какую версию выбрал бы загрузчик по списку из файла.
            options['mode'] = 'explain-select'
            options['explain_select'] = argv[index + 1]
            index += 1
        else:
            raise Refused(f'Неизвестный ключ: {arg}')
        index += 1
    return options


# ---------- openssl ----------

def openssl():
    found = os.environ.get('BURGEROS_OPENSSL') or shutil.which('openssl')
    if not found:
        raise Refused('Нужна команда openssl (она есть в Ubuntu 24.04)')
    return found


def key_id(pem):
    der = subprocess.run([openssl(), 'pkey', '-pubin', '-outform', 'DER'], input=pem.encode(),
                         capture_output=True, check=False)
    if der.returncode != 0:
        raise Refused('Ключ в цепочке повреждён')
    return hashlib.sha256(der.stdout).hexdigest()


def verify(pem, data, signature):
    if len(signature) != 64:
        return False
    with tempfile.TemporaryDirectory() as work:
        files = {'key.pem': pem.encode(), 'data': data, 'sig': signature}
        for name, content in files.items():
            with open(os.path.join(work, name), 'wb') as handle:
                handle.write(content)
        result = subprocess.run([openssl(), 'pkeyutl', '-verify', '-pubin', '-inkey', os.path.join(work, 'key.pem'),
                                 '-rawin', '-in', os.path.join(work, 'data'), '-sigfile', os.path.join(work, 'sig')],
                                capture_output=True, check=False)
        return result.returncode == 0


# ---------- цепочка ключей (BX-7) ----------

def verify_chain(chain, newest_accepted=None):
    if not isinstance(chain, dict) or not isinstance(chain.get('links'), list):
        raise Refused('Цепочка ключей повреждена')
    root_id = key_id(KEYCHAIN['root'])
    if key_id(chain.get('root', '')) != root_id:
        raise Refused('Цепочка ключей начинается не с ключа этой коробки')
    keys = [{'id': root_id, 'pem': KEYCHAIN['root'], 'index': 0}]
    for link in chain['links']:
        previous = keys[-1]
        next_id = key_id(link.get('key', ''))
        message = f'BURGEROS-KEYLINK-1 {previous["id"]} {next_id}\n'.encode()
        if not verify(previous['pem'], message, base64.b64decode(link.get('signature', ''))):
            raise Refused('Звено цепочки ключей не подписано предыдущим ключом')
        if any(key['id'] == next_id for key in keys):
            raise Refused('Ключ повторяется в цепочке')
        keys.append({'id': next_id, 'pem': link['key'], 'index': len(keys)})
    if newest_accepted and not any(key['id'] == newest_accepted for key in keys):
        raise Refused('В цепочке нет ключа, который этот сервер уже принял')
    return keys


def key_in(keys, wanted):
    for key in keys:
        if key['id'] == wanted:
            return key
    raise Refused('Документ подписан ключом не из цепочки коробки')


def own_newest_key():
    # Загрузчик сам знает цепочку; новейший из неё — нижняя граница для списков.
    keys = verify_chain(KEYCHAIN)
    return keys[-1]['id']


def newest_accepted():
    accepted_file = os.path.join(STATE, 'signing-key-current')
    candidates = [own_newest_key()]
    if os.path.exists(accepted_file):
        candidates.append(open(accepted_file, encoding='utf-8').read().strip())
    return candidates


# ---------- лицензионный блок (BX-9) ----------

def decode_license(block):
    compact = re.sub(r'\s+', '', block)
    if not compact.startswith(LICENSE_PREFIX):
        raise Refused('Это не лицензионный блок BurgerOS')
    try:
        envelope = json.loads(base64.b64decode(compact[len(LICENSE_PREFIX):], validate=True))
        payload_bytes = base64.b64decode(envelope['payload'], validate=True)
        payload = json.loads(payload_bytes)
        signature = base64.b64decode(envelope['signature'], validate=True)
    except Exception:
        raise Refused('Лицензионный блок повреждён — вставьте его целиком ещё раз')
    keys = verify_chain(envelope.get('keychain'))
    signer = key_in(keys, payload.get('signedBy'))
    if not verify(signer['pem'], payload_bytes, signature):
        raise Refused('Подпись лицензионного блока неверна')
    for field in ('kind', 'buyer', 'name', 'issued', 'repo', 'deployKey'):
        if not isinstance(payload.get(field), str) or not payload[field]:
            raise Refused('Лицензионный блок повреждён')
    return payload


# ---------- версии и выбор (BX-5, BX-28) ----------

VERSION = re.compile(r'^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)'
                     r'(?:-((?:0|[1-9]\d*|\d*[A-Za-z-][0-9A-Za-z-]*)(?:\.(?:0|[1-9]\d*|\d*[A-Za-z-][0-9A-Za-z-]*))*))?$')


def parse_version(text):
    match = VERSION.match(text or '')
    if not match:
        raise Refused(f'Номер версии «{text}» не по правилу')
    tail = [int(part) if part.isdigit() else part for part in match.group(4).split('.')] if match.group(4) else []
    return [int(match.group(1)), int(match.group(2)), int(match.group(3))], tail


def compare_versions(left, right):
    (a, a_tail), (b, b_tail) = parse_version(left), parse_version(right)
    if a != b:
        return -1 if a < b else 1
    if not a_tail and not b_tail:
        return 0
    if not a_tail:
        return 1
    if not b_tail:
        return -1
    for index in range(max(len(a_tail), len(b_tail))):
        if index >= len(a_tail):
            return -1
        if index >= len(b_tail):
            return 1
        x, y = a_tail[index], b_tail[index]
        if x == y:
            continue
        if isinstance(x, int) and isinstance(y, int):
            return -1 if x < y else 1
        if isinstance(x, int):
            return -1
        if isinstance(y, int):
            return 1
        return -1 if x < y else 1
    return 0


def position(entry):
    return entry.get('replaces') or entry['version']


def queue_position(installed, versions):
    for entry in versions:
        if entry['version'] == installed:
            return entry.get('replaces') or installed
    return installed


def eligible(installed, entry, versions):
    if entry.get('replacedBy'):
        return False
    if installed is None:
        return True
    if entry['version'] == installed:
        return False
    here = queue_position(installed, versions)
    if entry.get('replaces'):
        return compare_versions(here, entry['replaces']) <= 0
    return compare_versions(entry['version'], here) > 0


sort_key = functools.cmp_to_key(lambda a, b: compare_versions(position(a), position(b))
                                or compare_versions(a['version'], b['version']))


def select_next(installed, versions, promoted_only=False):
    pool = [entry for entry in versions if not promoted_only or entry.get('status') == 'promoted']
    pool = sorted([entry for entry in pool if eligible(installed, entry, versions)], key=sort_key)
    if not pool:
        return None
    stops = [entry for entry in pool if entry.get('stop')]
    if not stops:
        return pool[-1]
    # Несколько остановок на одном месте — замены X′, X″ одной X: новейшая.
    return [entry for entry in stops if compare_versions(position(entry), position(stops[0])) == 0][-1]


def select_latest(versions, promoted_only=False):
    pool = [entry for entry in versions
            if (not promoted_only or entry.get('status') == 'promoted') and not entry.get('replacedBy')]
    pool = sorted(pool, key=sort_key)
    return pool[-1] if pool else None


# ---------- список выпусков (BX-8) ----------

# Какой список читает сервер с блоком этого вида (BX-8, BX-29). Канал входит в
# подпись: подлинный список кандидатов, переложенный в репозиторий покупателей,
# иначе открыл бы им непродвинутый или отозванный выпуск.
CHANNEL_FOR_LICENSE = {'buyer': 'releases', 'stand': 'candidates', 'test': 'test'}


def verify_list(data, signature, channel):
    try:
        listing = json.loads(data)
    except Exception:
        raise Refused('Список выпусков не читается')
    if listing.get('core') != LIST_CORE or not isinstance(listing.get('versions'), list):
        raise Refused('Список выпусков повреждён')
    if listing.get('channel') != channel:
        raise Refused(f'Это список выпусков «{listing.get("channel")}», а этому серверу нужен «{channel}»')
    accepted = [key for key in newest_accepted() if key]
    keys = verify_chain(listing.get('keychain'))
    for known in accepted:
        # Ключ, который загрузчик или сервер уже принял, обязан стоять в цепочке,
        # а список — быть подписан им или более новым (BX-7).
        known_key = key_in(keys, known)
        signer = key_in(keys, listing.get('signedBy'))
        if signer['index'] < known_key['index']:
            raise Refused('Список выпусков подписан ключом старше того, что уже принят')
    signer = key_in(keys, listing.get('signedBy'))
    if not verify(signer['pem'], data, signature):
        raise Refused('Подпись списка выпусков неверна')
    seen = set()
    for entry in listing['versions']:
        parse_version(entry.get('version'))
        if entry['version'] in seen:
            raise Refused('Список выпусков повреждён: номер версии')
        seen.add(entry['version'])
    return listing, keys


# ---------- git ----------

def git(args, env=None, capture=True):
    result = subprocess.run(['git', *args], capture_output=capture, env={**os.environ, **(env or {})}, check=False)
    if result.returncode != 0:
        raise Refused('Нет доступа к выпускам: ' + (result.stderr.decode(errors='replace').strip()[-400:] if capture else ''))
    return result.stdout


def github_known_hosts(target):
    with urllib.request.urlopen('https://api.github.com/meta', timeout=30) as response:
        meta = json.load(response)
    lines = []
    for key in meta.get('ssh_keys', []):
        lines.append(f'github.com {key}')
        lines.append(f'[ssh.github.com]:443 {key}')
    with open(target, 'w', encoding='utf-8') as handle:
        handle.write('\n'.join(lines) + '\n')


class Releases:
    """Своя неполная копия репозитория выпусков: `main` и нужные метки (BX-8)."""

    def __init__(self, repo, deploy_key_file):
        self.repo = repo
        self.git_dir = os.path.join(SHARED, 'releases.git')
        os.makedirs(SHARED, exist_ok=True)
        if not os.path.exists(self.git_dir):
            git(['init', '--bare', '-q', self.git_dir])
        known_hosts = os.path.join(SHARED, 'github_known_hosts')
        self.env = {}
        if 'github.com' in repo:
            if not os.path.exists(known_hosts):
                github_known_hosts(known_hosts)
            self.env['GIT_SSH_COMMAND'] = (f'ssh -i {deploy_key_file} -o IdentitiesOnly=yes -o BatchMode=yes '
                                           f'-o UserKnownHostsFile={known_hosts} -o StrictHostKeyChecking=yes')

    def fetch(self, ref):
        git(['--git-dir', self.git_dir, 'fetch', '--quiet', '--depth', '1', '--force', self.repo, ref], env=self.env)

    def show(self, rev, name):
        return git(['--git-dir', self.git_dir, 'show', f'{rev}:{name}'])

    def archive(self, version):
        return git(['--git-dir', self.git_dir, 'archive', f'refs/tags/v{version}'])


# ---------- распаковка и сверка ----------

def safe_extract(archive_bytes, target):
    with tarfile.open(fileobj=io.BytesIO(archive_bytes)) as archive:
        members = archive.getmembers()
        for member in members:
            name = member.name
            parts = name.split('/')
            if name.startswith('/') or '..' in parts or '' in parts[:-1] or '\\' in name:
                raise Refused(f'В архиве выпуска недопустимый путь: {name}')
            if not (member.isfile() or member.isdir()):
                raise Refused(f'В архиве выпуска запись недопустимого вида: {name}')
        try:
            archive.extractall(target, members=members, filter='data')
        except TypeError:
            # Python старше 3.12 фильтра не знает; записи уже проверены выше.
            archive.extractall(target, members=members)


def file_hashes(root, skip=('manifest.json', 'manifest.sig')):
    found = {}
    for directory, dirs, files in os.walk(root):
        for name in dirs + files:
            full = os.path.join(directory, name)
            if os.path.islink(full):
                raise Refused(f'В выпуске ссылка: {os.path.relpath(full, root)}')
        for name in files:
            full = os.path.join(directory, name)
            relative = os.path.relpath(full, root).replace(os.sep, '/')
            if relative in skip:
                continue
            with open(full, 'rb') as handle:
                found[relative] = hashlib.sha256(handle.read()).hexdigest()
    return found


def check_manifest(listing, keys, version, manifest_bytes, signature):
    entry = next((item for item in listing['versions'] if item['version'] == version), None)
    if entry is None:
        raise Refused(f'Версии {version} нет в подписанном списке выпусков')
    signer = key_in(keys, entry.get('signedBy'))
    if not verify(signer['pem'], manifest_bytes, signature):
        raise Refused('Подпись описания выпуска неверна')
    if hashlib.sha256(manifest_bytes).hexdigest() != entry.get('manifestSha256'):
        raise Refused('Описание выпуска не то, что в подписанном списке')
    manifest = json.loads(manifest_bytes)
    if manifest.get('core') != MANIFEST_CORE:
        raise Refused('Этот выпуск требует более нового загрузчика: скачайте его заново по памятке')
    if manifest.get('version') != version:
        raise Refused(f'Метка v{version} стоит на выпуске с описанием {manifest.get("version")}')
    if not isinstance(manifest.get('files'), dict) or not isinstance(manifest.get('bun'), dict):
        raise Refused('Описание выпуска повреждено')
    return manifest


def verify_tree(root, manifest):
    actual = file_hashes(root)
    expected = manifest['files']
    if actual != expected:
        missing = sorted(set(expected) - set(actual))[:5]
        extra = sorted(set(actual) - set(expected))[:5]
        changed = sorted(name for name in expected if name in actual and actual[name] != expected[name])[:5]
        raise Refused(f'Выпуск не совпадает с описанием. нет: {missing}; лишние: {extra}; изменены: {changed}')


# ---------- Bun (BX-12, шаг 4) ----------

def cpu_build():
    try:
        flags = open('/proc/cpuinfo', encoding='utf-8').read()
    except OSError:
        return 'x64'
    return 'x64' if re.search(r'\bavx2\b', flags) else 'x64-baseline'


def install_bun(manifest):
    bun = manifest['bun']
    build_name = cpu_build()
    build = bun['builds'].get(build_name)
    if not build:
        raise Refused(f'В выпуске нет сборки Bun для этого процессора ({build_name})')
    target_dir = path('/opt/burgeros/bun', bun['version'])
    target = os.path.join(target_dir, 'bun')
    if os.path.exists(target) and hashlib.sha256(open(target, 'rb').read()).hexdigest() == build['sha256']:
        return target, build_name
    with urllib.request.urlopen(build['url'], timeout=300) as response:
        archive = response.read()
    with zipfile.ZipFile(io.BytesIO(archive)) as bundle:
        member = next((name for name in bundle.namelist() if name.endswith('/bun')), None)
        if member is None:
            raise Refused('В архиве Bun нет исполняемого файла')
        binary = bundle.read(member)
    if hashlib.sha256(binary).hexdigest() != build['sha256']:
        raise Refused('Отпечаток Bun не совпал с подписанным описанием выпуска')
    os.makedirs(target_dir, exist_ok=True)
    temporary = target + '.part'
    with open(temporary, 'wb') as handle:
        handle.write(binary)
    os.chmod(temporary, 0o755)
    os.replace(temporary, target)
    return target, build_name


# ---------- ответы ----------

def ask(question, device='/dev/tty'):
    # Веб-консоль хостинга (опыт D2f) — последовательный порт: Enter там
    # приходит как «\r» или «\r\n». Хвост Enter от набранной команды ждал в
    # очереди и читался пустым ответом, а «\r» без перевода в «\n» строку не
    # заканчивает. Поэтому очередь перед вопросом сбрасывается, «\r» считается
    # концом строки, а пустые строки пропускаются.
    try:
        fd = os.open(device, os.O_RDWR | os.O_NOCTTY)
    except OSError:
        return None
    saved = None
    try:
        try:
            saved = termios.tcgetattr(fd)
            mode = termios.tcgetattr(fd)
            mode[0] = (mode[0] | termios.ICRNL) & ~termios.IGNCR
            mode[3] |= termios.ICANON
            termios.tcsetattr(fd, termios.TCSANOW, mode)
            termios.tcflush(fd, termios.TCIFLUSH)
        except termios.error:
            saved = None
        os.write(fd, question.encode('utf-8'))
        with open(fd, 'r', encoding='utf-8', closefd=False) as tty:
            while True:
                line = tty.readline()
                if not line:
                    return None
                if line.strip():
                    return line.strip()
    finally:
        if saved is not None:
            termios.tcsetattr(fd, termios.TCSANOW, saved)
        os.close(fd)


def collect_answers(options):
    if options['mode'] == 'update':
        license_file = os.path.join(SHARED, 'license')
        if not os.path.exists(license_file):
            raise Refused('На сервере нет лицензионного блока: /opt/burgeros/shared/license')
        return open(license_file, encoding='utf-8').read(), None, None
    block = open(options['license_file'], encoding='utf-8').read() if options['license_file'] else None
    domain, email = options['domain'], options['email']
    if block is None:
        block = ask('Вставьте лицензионный блок (одна строка BURGEROS-LICENSE-1:…) и нажмите Enter:\n')
    if domain is None:
        domain = ask('Домен, на котором будет работать продукт (например crm.example.ru): ')
    if email is None:
        email = ask('Почта для писем Let\'s Encrypt о сертификате: ')
    if not block or not domain or not email:
        raise Refused('Не хватает ответов, а спросить негде (нет терминала). '
                      'Запустите с ключами: --license-file <файл> --domain <домен> --email <почта>')
    return block, normalize_domain(domain), normalize_email(email)


DOMAIN = re.compile(r'(?=.{1,253}$)([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\.)+([a-z]{2,63}|xn--[a-z0-9-]{1,59})')


def normalize_domain(text):
    # Домен на кириллице (`crm.магазин.рф`) переводится в запись IDNA
    # (`crm.xn--80aswg.xn--p1ai`): её понимают certbot, nginx, Let's Encrypt, а
    # браузер присылает в заголовке Origin именно её — с ней сверяется CORS_ORIGINS.
    domain = text.strip().lower().rstrip('.')
    try:
        domain = domain.encode('idna').decode('ascii')
    except UnicodeError:
        raise Refused(f'«{text.strip()}» не похоже на домен (пример: crm.example.ru)')
    if not DOMAIN.fullmatch(domain):
        raise Refused(f'«{text.strip()}» не похоже на домен (пример: crm.example.ru)')
    return domain


def normalize_email(text):
    email = text.strip()
    if not re.fullmatch(r'[^@\s]+@[^@\s]+\.[^@\s]+', email):
        raise Refused(f'«{email}» не похоже на адрес почты')
    return email


def write_secret(target, content):
    os.makedirs(os.path.dirname(target), exist_ok=True)
    temporary = target + '.part'
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, 'w', encoding='utf-8') as handle:
        handle.write(content)
    os.chmod(temporary, 0o600)
    os.replace(temporary, target)


BACKUP_NAME = re.compile(r'^web_app_demo-(.+)-(\d{8})-(\d{6})\.sql\.gz$')


def backup_version(file):
    # Каждая копия коробки знает свою версию (BX-26): в имени и первой строкой.
    if not file:
        raise Refused('Укажите файл копии: bash install.sh --restore <файл копии>')
    if not os.path.isfile(file):
        raise Refused(f'Файла копии нет: {file}')
    match = BACKUP_NAME.match(os.path.basename(file))
    if not match:
        raise Refused('Это не копия коробки: в имени нет версии (нужно web_app_demo-<версия>-<дата>.sql.gz)')
    version = match.group(1)
    parse_version(version)
    import gzip
    try:
        with gzip.open(file, 'rt', encoding='utf-8', errors='replace') as handle:
            first = handle.readline().strip()
    except OSError:
        raise Refused('Файл копии повреждён или не сжат gzip')
    if first != f'-- BurgerOS version {version}':
        raise Refused(f'Версия внутри копии не совпадает с именем файла ({version}) — копию переименовали?')
    return version


def installed_version():
    manifest = path('/opt/burgeros/current/manifest.json')
    if not os.path.exists(manifest):
        return None
    return json.load(open(manifest, encoding='utf-8'))['version']



# ---------- проверки сервера (BX-10, пункт 2) ----------

def sandboxed():
    # Песочница проверок загрузчика (BURGEROS_ROOT): там нет ни Ubuntu, ни
    # nginx, и проверки сервера и домена не выполняются.
    return ROOT != '/'


def os_release():
    try:
        text = open('/etc/os-release', encoding='utf-8').read()
    except OSError:
        return {}
    values = {}
    for line in text.splitlines():
        if '=' in line:
            key, value = line.split('=', 1)
            values[key] = value.strip().strip('"')
    return values


def foreign_burgeros():
    # Сервер владельца app.burgeros.ru носит те же имена (BX-2).
    if os.path.exists(path('/opt/burgeros/shared/install.env')):
        return None
    for marker in ('/opt/burgeros/.git', '/opt/burgeros/backend/.env', '/etc/systemd/system/burgeros-backend.service'):
        if os.path.exists(path(marker)):
            return marker
    # Тома Docker песочницы не видны: на машине владельца живёт база разработки
    # с тем же именем проекта.
    if not sandboxed() and shutil.which('docker'):
        volumes = subprocess.run(['docker', 'volume', 'ls', '-q', '--filter', 'label=com.docker.compose.project=burgeros'],
                                 capture_output=True, check=False)
        if volumes.returncode == 0 and volumes.stdout.strip():
            return 'том Docker проекта burgeros'
    return None


# Порог свободного места (BX-10): 15 ГБ — для чистого сервера. Коробка, уже
# стоявшая здесь (повтор оборванной установки, обновление, установка заново после
# burgeros-wipe), сама заняла несколько гигабайт подкачкой, пакетами и образом
# базы — с ней хватает места на выпуск и копию базы.
CLEAN_SERVER_FREE = 15 * 1000 ** 3
BOX_SERVER_FREE = 4 * 1000 ** 3
# Следы коробки, которые остаются и после burgeros-wipe.
BOX_TRACES = ('/opt/burgeros/shared/install.env', '/var/lib/burgeros', '/etc/fail2ban/jail.d/burgeros.local')


def box_was_here():
    return any(os.path.exists(path(trace)) for trace in BOX_TRACES)


def min_free_bytes(box_present):
    return BOX_SERVER_FREE if box_present else CLEAN_SERVER_FREE


# Выпуски Ubuntu LTS, на которых проверена установка. 26.04 добавлена по
# решению владельца 22.10.2026: хостинги уже ставят её по умолчанию.
SUPPORTED_UBUNTU = ('24.04', '26.04')


def update_in_progress():
    """Идёт ли обновление: открытый журнал, заявка, живой замок или идущее звено переезда."""
    journal_file = path('/var/lib/burgeros/update-journal')
    if os.path.exists(journal_file) and not json.load(open(journal_file, encoding='utf-8')).get('closed'):
        return 'Прошлое обновление не закончено.'
    # Идущая работа — открытый журнал или живой процесс в общем замке. Заявка и
    # «служба запущена» — не признак: падающая по кругу служба почти всегда
    # «activating», а это ровно случай для запасного выхода. Свежую заявку
    # установщик под замком перепишет своей — она уйдёт той же службе.
    try:
        pid = int(open(path('/run/burgeros-update.lock/pid'), encoding='utf-8').read().strip() or 0)
    except (OSError, ValueError):
        pid = 0
    if pid > 0:
        try:
            os.kill(pid, 0)
            return 'Обновление, проверка версий или доводка сейчас идёт.'
        except ProcessLookupError:
            pass
        except PermissionError:
            return 'Обновление, проверка версий или доводка сейчас идёт.'
    return None


def server_checks(options):
    if os.path.exists(path('/var/lib/burgeros-wipe-in-progress')):
        raise Refused('Стирание прежней установки не закончено — запустите burgeros-wipe ещё раз.')
    found = foreign_burgeros()
    if found:
        raise Refused(f'На сервере уже работает BurgerOS, установленный не коробкой ({found}); коробку на него ставить нельзя.')
    # Переезд с незаконченной цепочкой обновлений (BX-26) законченной установкой не
    # считается: обычный запуск и --restore отказывают, --restore --continue — только тогда.
    chain_file = path('/var/lib/burgeros/restore-chain')
    chain_open = os.path.exists(chain_file) and json.load(open(chain_file, encoding='utf-8')).get('state') != 'finished'
    if options['mode'] == 'restore' and options['continue']:
        if not chain_open:
            raise Refused('Незаконченного переезда на этом сервере нет.')
        return
    if chain_open and options['mode'] in ('install', 'restore'):
        raise Refused('Переезд не закончен — продолжите его: bash install.sh --restore --continue')
    if options['mode'] == 'update':
        # Запасной выход раскладывает выпуск в /opt/burgeros/releases — ту же папку,
        # в которой может работать идущее обновление (или звено переезда). Пока оно
        # идёт, ничего не трогаем: иначе служба потеряла бы подготовленную папку.
        busy = update_in_progress()
        if busy:
            raise Refused(f'{busy} Ход: burgeros-update --status; если оно застряло — burgeros-update --recover.')

    if options['mode'] in ('install', 'restore') and os.path.exists(path('/var/lib/burgeros/install-done')):
        raise Refused('Продукт уже установлен. Новая версия ставится командой burgeros-update --request '
                      '(или кнопкой «Обновить» в настройках, когда она появится); '
                      'если обновление застряло — burgeros-update --recover.')
    journal_file = path('/var/lib/burgeros/install-journal.json')
    if options['mode'] != 'update' and os.path.exists(journal_file):
        journal = json.load(open(journal_file, encoding='utf-8'))
        # Два варианта стенда — разные режимы журнала, как у установщика (checks.ts).
        if options['stand']:
            mode = 'stand-restore' if options['mode'] == 'restore' else 'stand'
        else:
            mode = options['mode']
        if not journal.get('closed') and journal.get('mode') != mode:
            repeat = {'install': 'bash install.sh', 'restore': 'bash install.sh --restore <копия>',
                      'stand': 'bash install.sh --stand', 'stand-restore': 'bash install.sh --stand --restore <копия>'}
            raise Refused('Прошлый запуск был в другом режиме и не закончен — повторите ту же команду: '
                          + repeat.get(journal.get('mode'), 'ту же, что в прошлый раз') + '.')
    if sandboxed():
        return
    problems = []
    if os.geteuid() != 0:
        problems.append('Команду нужно запускать от root.')
    release = os_release()
    if release.get('ID') != 'ubuntu' or release.get('VERSION_ID') not in SUPPORTED_UBUNTU:
        problems.append(f'Нужна Ubuntu {" или ".join(SUPPORTED_UBUNTU)}, а на сервере {release.get("ID", "?")} {release.get("VERSION_ID", "?")}.')
    machine = os.uname().machine
    if machine != 'x86_64':
        problems.append(f'Серверы на процессоре {machine} пока не поддерживаются — нужен x86_64.')
    try:
        mem_kib = int(re.search(r'^MemTotal:\s+(\d+)', open('/proc/meminfo').read(), re.M).group(1))
    except Exception:
        mem_kib = 0
    if mem_kib < int(1.7 * 1024 * 1024):
        problems.append(f'Памяти {mem_kib / 1024 / 1024:.1f} ГиБ, нужно не меньше 2 ГБ.')
    free = shutil.disk_usage('/').free
    need = min_free_bytes(options['mode'] == 'update' or box_was_here())
    if free < need:
        problems.append(f'Свободно {free / 1000 ** 3:.1f} ГБ на диске, нужно не меньше {need // 1000 ** 3} ГБ.')
    if problems:
        raise Refused('сервер не подходит:\n  ' + '\n  '.join(problems))


def wait_for_fresh_server():
    # Первые минуты после создания сервера система сама ставит обновления и
    # держит менеджер пакетов (BX-10, пункт 2). Ждём до 20 минут.
    if sandboxed() or not shutil.which('cloud-init'):
        return
    status = subprocess.run(['cloud-init', 'status'], capture_output=True, text=True, check=False).stdout
    if 'running' not in status and 'not started' not in status:
        return
    say('Сервер ещё готовится после создания — ждём, это до нескольких минут…')
    try:
        subprocess.run(['cloud-init', 'status', '--wait'], capture_output=True, check=False, timeout=1200)
    except subprocess.TimeoutExpired:
        raise Refused('Сервер не закончил первую настройку за 20 минут. Запустите команду через несколько минут.')


APT_ENV = {**os.environ, 'DEBIAN_FRONTEND': 'noninteractive', 'NEEDRESTART_MODE': 'a'}


def apt_install(packages):
    missing = [name for name in packages
               if 'install ok installed' not in subprocess.run(['dpkg-query', '-W', '-f=${Status}', name],
                                                              capture_output=True, text=True, check=False).stdout]
    if not missing:
        return
    lock = ['-o', 'DPkg::Lock::Timeout=1200']
    for args in (['update'], ['install', '-y', '--no-install-recommends', *missing]):
        # DPkg::Lock::Timeout не ждёт замок списков /var/lib/apt/lists/lock: на
        # свежем сервере его в первые минуты держат службы Ubuntu — ждём сами.
        give_up_at = time.monotonic() + 1200
        while True:
            result = subprocess.run(['apt-get', *lock, *args], capture_output=True, text=True, env=APT_ENV, check=False)
            if result.returncode == 0:
                break
            busy = 'Could not get lock' in result.stderr or 'Unable to lock directory' in result.stderr
            if not busy or time.monotonic() > give_up_at:
                raise Refused('Менеджер пакетов не поставил ' + ', '.join(missing) + ':\n' + result.stderr.strip()[-600:])
            time.sleep(10)


# ---------- проверка домена (BX-10, пункт 4) ----------

def server_addresses():
    result = subprocess.run(['ip', '-j', 'addr'], capture_output=True, text=True, check=False)
    v4, v6 = set(), set()
    try:
        interfaces = json.loads(result.stdout or '[]')
    except ValueError:
        interfaces = []
    for interface in interfaces:
        for item in interface.get('addr_info', []):
            if item.get('scope') != 'global':
                continue
            (v4 if item.get('family') == 'inet' else v6).add(item.get('local'))
    return v4, v6


def shown_addresses(v4, v6):
    # Человеку — только адреса, которые можно вписать у регистратора: внутренний
    # мост Docker (172.17.0.1) в подсказке сбивал бы с толку.
    public = sorted(item for item in v4 | v6 if ipaddress.ip_address(item).is_global)
    return ', '.join(public or sorted(v4 | v6)) or 'не виден на сервере'


def resolve(domain, family):
    try:
        return {info[4][0] for info in socket.getaddrinfo(domain, None, family, socket.SOCK_STREAM)}
    except socket.gaierror:
        return set()


TEMPORARY_SITE = r"""# Временный сайт коробки BurgerOS (BX-15): только HTTP, пока нет сертификата.
server {
    listen 80;
    listen [::]:80;
    server_name __DOMAIN__;

    location ^~ /.well-known/acme-challenge/ {
        root /var/www/burgeros-acme;
        default_type text/plain;
    }

    location / {
        default_type text/plain;
        return 200 "BurgerOS: идёт установка\n";
    }
}
"""


def certificate_valid(domain):
    cert = f'/etc/letsencrypt/live/{domain}/fullchain.pem'
    if not os.path.exists(cert):
        return False
    return subprocess.run([openssl(), 'x509', '-checkend', str(30 * 24 * 3600), '-noout', '-in', cert],
                          capture_output=True, check=False).returncode == 0


def explain_trial_failure(domain, email, shown, output):
    # Пробный выпуск отказывает не только из-за домена: Let's Encrypt не берёт
    # почту с опечаткой в зоне или запрещённым доменом, запись CAA может запрещать
    # ему выпуск, у него самого бывают сбои. Свалить всё на домен значило бы
    # отправить человека проверять DNS по кругу — поэтому причина называется, а
    # хвост ответа certbot показывается всегда.
    text = output.lower()
    tail = '\n'.join(line for line in output.strip().splitlines()[-8:] if line.strip())
    details = f'\nОтвет certbot:\n{tail}\nПодробно: /var/log/letsencrypt/letsencrypt.log' if tail else \
        '\nПодробно: /var/log/letsencrypt/letsencrypt.log'
    if 'invalidcontact' in text or 'unsupportedcontact' in text or 'invalid email' in text or 'contact email' in text:
        return (f'Let\'s Encrypt не принимает почту «{email}» — проверьте, нет ли в ней опечатки, '
                'и укажите настоящий адрес. Запустите команду снова.' + details)
    if 'caa' in text:
        return (f'Запись CAA у домена {domain} запрещает Let\'s Encrypt выдавать сертификат. Разрешите '
                'letsencrypt.org в записи CAA у регистратора или удалите её. Запустите команду снова.' + details)
    # Запись A к этому часу уже сверена с адресом сервера: молчание порта 80 — это
    # почти всегда межсетевой экран хостинга, а не DNS.
    if 'timeout during connect' in text or 'firewall' in text or 'connection refused' in text:
        return (f'Let\'s Encrypt не достучался до сервера по порту 80 — похоже, порт закрыт межсетевым экраном. '
                'Откройте порты 80 и 443 в панели хостинга (раздел «Межсетевой экран» или «Firewall») и '
                f'запустите команду снова. Если они открыты — проверьте, что запись A домена {domain} ведёт на {shown}.'
                + details)
    return (f'Домен {domain} пока недоступен из интернета на этом сервере (адрес сервера: {shown}). '
            'Проверьте записи A и AAAA у регистратора (после изменения может пройти до нескольких часов) '
            'и что порты 80 и 443 открыты в панели хостинга. Запустите команду снова.' + details)


def domain_check(domain, email):
    if sandboxed():
        return
    say(f'Проверяю домен {domain}…')
    own_v4, own_v6 = server_addresses()
    shown = shown_addresses(own_v4, own_v6)
    records_a, records_aaaa = resolve(domain, socket.AF_INET), resolve(domain, socket.AF_INET6)
    if not records_a:
        raise Refused(f'У домена {domain} нет записи A. Направьте её у регистратора на адрес сервера ({shown}) '
                      'и запустите команду снова (запись расходится до нескольких часов).')
    public_v4 = {item for item in own_v4 if not ipaddress.ip_address(item).is_private}
    if public_v4 and not (records_a & public_v4):
        raise Refused(f'Запись A домена {domain} ведёт на {", ".join(sorted(records_a))}, а адрес этого сервера — '
                      f'{", ".join(sorted(public_v4))}. Исправьте запись у регистратора и запустите команду снова.')
    if not public_v4:
        say('Предупреждение: публичный адрес на самом сервере не виден (хостинг прячет его) — запись A проверит пробный сертификат.')
    stray_aaaa = records_aaaa - own_v6
    if stray_aaaa:
        raise Refused(f'У домена есть запись AAAA (IPv6) {", ".join(sorted(stray_aaaa))}, которая ведёт не на этот сервер. '
                      'Удалите её у регистратора или направьте на адрес IPv6 сервера'
                      + (f': {", ".join(sorted(own_v6))}' if own_v6 else ' (у этого сервера IPv6 нет)') + '.')

    if certificate_valid(domain):
        say(f'Сертификат на {domain} уже есть — пробный выпуск не нужен.')
        return
    apt_install(['nginx', 'certbot'])
    os.makedirs('/var/www/burgeros-acme', exist_ok=True)
    site = '/etc/nginx/sites-available/burgeros'
    if not os.path.exists(site) or 'acme-challenge' not in open(site, encoding='utf-8').read():
        with open(site, 'w', encoding='utf-8') as handle:
            handle.write(TEMPORARY_SITE.replace('__DOMAIN__', domain))
    if not os.path.lexists('/etc/nginx/sites-enabled/burgeros'):
        os.symlink(site, '/etc/nginx/sites-enabled/burgeros')
    if os.path.lexists('/etc/nginx/sites-enabled/default'):
        os.remove('/etc/nginx/sites-enabled/default')
    for command in (['nginx', '-t'], ['systemctl', 'enable', '--now', 'nginx'], ['systemctl', 'reload', 'nginx']):
        result = subprocess.run(command, capture_output=True, text=True, check=False)
        if result.returncode != 0:
            raise Refused('nginx не запустился: ' + result.stderr.strip()[-400:])
    # Пробный выпуск — к тестовому серверу Let's Encrypt: он стучится на домен из
    # интернета, и в предел неудачных попыток настоящего сервера не засчитывается.
    trial = subprocess.run(['certbot', 'certonly', '--webroot', '-w', '/var/www/burgeros-acme', '-d', domain,
                            '-m', email, '--agree-tos', '-n', '--dry-run'],
                           capture_output=True, text=True, check=False)
    if trial.returncode != 0:
        raise Refused(explain_trial_failure(domain, email, shown, f'{trial.stdout}\n{trial.stderr}'))
    say(f'Домен {domain} ведёт на этот сервер, порт 80 открыт.')


# ---------- главное ----------

def main(argv):
    options = parse_args(argv)
    if options['mode'] == 'print-hash':
        say(hashlib.sha256(open(os.path.realpath(sys.argv[1]), 'rb').read()).hexdigest())
        return 0
    if options['mode'] == 'explain-select':
        listing = json.load(open(options['explain_select'], encoding='utf-8'))
        chosen = select_next(options['installed'], listing['versions']) if options['installed'] \
            else select_latest(listing['versions'])
        say(chosen['version'] if chosen else '-')
        return 0

    server_checks(options)
    if options['mode'] == 'restore' and options['continue']:
        # Цепочку ведёт служба обновления установленной версии; загрузчик её только будит.
        return subprocess.run(['/usr/local/bin/burgeros-update', '--chain-continue'], check=False).returncode
    if options['mode'] == 'restore':
        backup_version(options['restore'])
    block, domain, email = collect_answers(options)
    license_payload = decode_license(block)
    channel = CHANNEL_FOR_LICENSE.get(license_payload['kind'])
    if channel is None:
        raise Refused('Лицензионный блок неизвестного вида')
    # Кандидатов видит только стенд (BX-27): у покупателя в списке их нет, а
    # если окажутся — не ставятся.
    promoted_only = license_payload['kind'] != 'stand'
    # Запасной выход посреди переезда стенда — звено цепочки: только продвинутые,
    # как у службы обновления (BX-26); кандидат встаёт на стенд только кнопкой.
    chain_file = path('/var/lib/burgeros/restore-chain')
    if options['mode'] == 'update' and os.path.exists(chain_file) and \
            json.load(open(chain_file, encoding='utf-8')).get('state') != 'finished':
        promoted_only = True
    # Стенд — только своим блоком и только ключом --stand (BX-27): блок стенда
    # открывает кандидатов, и обычная установка с ним стала бы стендом молча.
    if options['mode'] in ('install', 'restore'):
        if options['stand'] and license_payload['kind'] != 'stand':
            raise Refused('Ключ --stand — только с лицензионным блоком стенда (release:buyer add --stand).')
        if not options['stand'] and license_payload['kind'] == 'stand':
            raise Refused('Это лицензионный блок стенда выпусков — он ставится только с ключом --stand.')
    say(f'Лицензия {license_payload["buyer"]} ({license_payload["name"]}) — подпись верна.')

    if options['mode'] != 'update':
        wait_for_fresh_server()
        domain_check(domain, email)

    deploy_key_file = os.path.join(SHARED, 'deploy_key')
    if options['mode'] != 'update':
        write_secret(os.path.join(SHARED, 'license'), re.sub(r'\s+', '', block) + '\n')
        write_secret(deploy_key_file, license_payload['deployKey'])

    with tempfile.TemporaryDirectory(prefix='burgeros-loader-') as work:
        if options['from_file']:
            bundle_dir = os.path.join(work, 'bundle')
            os.makedirs(bundle_dir)
            safe_extract(open(options['from_file'], 'rb').read(), bundle_dir)
            listing_bytes = open(os.path.join(bundle_dir, 'releases.json'), 'rb').read()
            listing_sig = open(os.path.join(bundle_dir, 'releases.sig'), 'rb').read()
            source = None
        else:
            source = Releases(license_payload['repo'], deploy_key_file)
            source.fetch('+refs/heads/main:refs/heads/main')
            listing_bytes = source.show('refs/heads/main', 'releases.json')
            listing_sig = source.show('refs/heads/main', 'releases.sig')
        listing, keys = verify_list(listing_bytes, listing_sig, channel)

        installed = installed_version() if options['mode'] == 'update' else None
        if options['mode'] == 'update':
            chosen = select_next(installed, listing['versions'], promoted_only)
            if chosen is None:
                say(f'Новых версий нет: установлена {installed}.')
                return 0
        elif options['mode'] == 'restore':
            # Переезд ставит ту версию, с которой снята копия, а не последнюю (BX-26).
            wanted = backup_version(options['restore'])
            chosen = next((entry for entry in listing['versions'] if entry['version'] == wanted), None)
            if chosen is None:
                raise Refused(f'Версии копии {wanted} нет в списке выпусков этой лицензии')
            # Стенд поднимается прямо на кандидата только при первом наполнении,
            # пока продвинутых выпусков нет (BX-27); дальше — с продвинутой версии.
            if chosen.get('status') != 'promoted' and \
                    any(entry.get('status') == 'promoted' for entry in listing['versions']):
                raise Refused(f'Версия копии {wanted} — кандидат: на стенд он встаёт только кнопкой «Обновить». '
                              'Поднимите стенд копией продвинутой версии.')
        else:
            chosen = select_latest(listing['versions'], promoted_only=True)
            if chosen is None and not promoted_only:
                chosen = select_latest(listing['versions'])
            if chosen is None:
                raise Refused('В списке выпусков нет ни одной версии')
        version = chosen['version']

        release_dir = os.path.join(work, 'release')
        os.makedirs(release_dir)
        if source is None:
            bundled = os.path.join(bundle_dir, 'release')
            manifest_bytes = open(os.path.join(bundled, 'manifest.json'), 'rb').read()
            signature = open(os.path.join(bundled, 'manifest.sig'), 'rb').read()
            if json.loads(manifest_bytes).get('version') != version:
                raise Refused(f'В пакете выпуска не та версия, что нужна этому серверу ({version})')
            manifest = check_manifest(listing, keys, version, manifest_bytes, signature)
            shutil.copytree(bundled, release_dir, dirs_exist_ok=True)
        else:
            source.fetch(f'+refs/tags/v{version}:refs/tags/v{version}')
            manifest_bytes = source.show(f'refs/tags/v{version}', 'manifest.json')
            signature = source.show(f'refs/tags/v{version}', 'manifest.sig')
            manifest = check_manifest(listing, keys, version, manifest_bytes, signature)
            safe_extract(source.archive(version), release_dir)
        verify_tree(release_dir, manifest)
        say(f'Выпуск {version}: подпись и отпечатки всех файлов верны.')

        bun_path, bun_build = install_bun(manifest)

        target = path('/opt/burgeros/releases', version)
        # «Уже работает» — отказ только для обновления. Недоведённая первая
        # установка или переезд (журнал не закрыт, `install-done` нет — это
        # проверено выше) могла оборваться уже после переключения `current` на
        # эту же версию, и повтор той же командой обязан её довести (BX-10).
        if options['mode'] == 'update' and \
                os.path.realpath(path('/opt/burgeros/current')) == os.path.realpath(target):
            raise Refused(f'Версия {version} уже работает')
        final_release = None
        if options['mode'] == 'update':
            # Запасной выход не трогает releases/<версия>: в ней может работать служба
            # обновления, запущенная, пока загрузчик скачивал выпуск. Выпуск ложится в
            # свою папку рядом, а на место его переносит установщик под общим замком,
            # проверив, что обновление не идёт (поле finalRelease — необязательное
            # дополнение стыка BX-12).
            final_release = target
            target = path('/opt/burgeros/releases', f'{version}.loader-{os.getpid()}')
        if os.path.exists(target):
            shutil.rmtree(target)
        os.makedirs(os.path.dirname(target), exist_ok=True)
        shutil.copytree(release_dir, target)

        answers = {
            'mode': options['mode'], 'stand': options['stand'],
            'restore': os.path.abspath(options['restore']) if options['restore'] else None,
            'continue': options['continue'], 'noChain': options['no_chain'], 'fromFile': options['from_file'],
            'domain': domain, 'email': email, 'licenseFile': os.path.join(SHARED, 'license'),
            'release': target, 'finalRelease': final_release, 'version': version, 'bun': bun_path, 'bunBuild': bun_build,
            'installed': installed, 'root': ROOT,
        }
        answers_file = os.path.join(work, 'answers.json')
        write_secret(answers_file, json.dumps(answers))
        result = subprocess.run([bun_path, os.path.join(target, 'box', 'installer.js'), '--answers', answers_file],
                                check=False)
        return result.returncode


try:
    sys.exit(main(sys.argv[2:]))
except Refused as refusal:
    print(f'Установка остановлена: {refusal}', file=sys.stderr, flush=True)
    sys.exit(EXIT_REFUSED)
except KeyboardInterrupt:
    print('Прервано.', file=sys.stderr)
    sys.exit(EXIT_REFUSED)
