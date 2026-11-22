#!/usr/bin/env python3
"""Look up module-sized replay tasks, reserve work and produce receipts."""
from collections import Counter
from pathlib import Path
from shutil import which
import argparse,datetime,gzip,hashlib,json,os,re,subprocess,sys,tarfile,time,urllib.request
base=Path(__file__).resolve().parent
repo='rohanarun/alpoge-rh-replay'
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
BUILT=re.compile(r'^\S+\s+\[\d+/\d+\]\s+Built\s+([^\s:]+)')
def rebuilt_imports(log_text,project,requested):
 """Project modules other than the requested targets that this Lake invocation reports as built."""
 log_text=re.sub(r'\x1b\[[0-9;]*m','',log_text)
 built={m[1] for m in map(BUILT.match,log_text.splitlines()) if m}
 return sorted(built.intersection(project)-set(requested))
def host_resources():
 """CPU count, total memory, and the peak resident set size of the largest finished child process."""
 info={'cpu_count':os.cpu_count()}
 try:
  with open('/proc/meminfo') as f:
   for line in f:
    if line.startswith('MemTotal:'):info['mem_total_kib']=int(line.split()[1]);break
 except OSError:pass
 try:
  import resource
  info['peak_child_rss_kib']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
 except ImportError:pass
 return info
def module_rows():
    with gzip.open(base / 'modules.jsonl.gz', 'rt') as stream:
        yield from map(json.loads, stream)

def load():
 rows=list(module_rows())
 completed=base/'completed.tsv'
 if completed.exists():
  import csv
  with completed.open() as f:done={r['id']:r['evidence'] for r in csv.DictReader(f,delimiter='\t')}
  for r in rows:
   if r['id'] in done:r['state']=done[r['id']]
 return rows
def select(rows, target, *, project_modules=None):
    """Collect matching targets and, for builds, the names needed to classify the transcript."""
    targets = []
    for row in rows:
        if project_modules is not None:
            project_modules.add(row['module'])
        if target in (row['id'], row['packet'], row['module']):
            targets.append(row)
    if not targets:
        raise SystemExit('Unknown task or packet: ' + target)
    return targets
def cold_modules(rows, busy):
    """Rank available tasks with no project imports by their available direct consumers."""
    available = [r for r in rows if r['state'] == 'open'
                 and r['id'] not in busy and r['packet'] not in busy]
    leaves = {r['id']: r for r in available if not r['imports']}
    sole = Counter()
    direct = Counter()
    for row in available:
        imports = set(row['imports'])
        for dep in imports:
            if dep in leaves:
                direct[dep] += 1
                if len(imports) == 1:
                    sole[dep] += 1
    ranked = sorted(leaves, key=lambda task: (-sole[task], -direct[task], task))
    return [(leaves[task], sole[task], direct[task]) for task in ranked]

def packet_suggestions(rows, busy, include_partial=False):
    """Split claimable packets into fully open and partially completed ones.

    A packet is fully open when every module is open. A partial packet has
    at least one open module while its remaining modules already carry
    evidence; it qualifies only when no module is assigned and neither the
    packet nor any of its modules is claimed. Packets appear in index order
    when fully open. Partial packets sort by depth, then by most open
    modules first. Each entry is (first open row, open count, total count).
    A partial packet cannot be claimed as a packet: the claim bot reserves
    every module that already has evidence, so its open modules are claimed
    individually instead.
    """
    groups = {}
    for r in rows:
        groups.setdefault(r['packet'], []).append(r)
    full = []
    partial = []
    for name, members in groups.items():
        if name in busy or any(r['id'] in busy for r in members):
            continue
        opened = [r for r in members if r['state'] == 'open']
        if not opened:
            continue
        entry = (opened[0], len(opened), len(members))
        if len(opened) == len(members):
            full.append(entry)
        elif include_partial and all(r['state'] != 'assigned' for r in members):
            partial.append(entry)
    partial.sort(key=lambda e: (e[0]['depth'], -e[1], e[0]['packet']))
    return full, partial

def authenticated_gh():
    cli = which('gh')
    # `auth status` fails if any saved account is invalid, even when the
    # active credential used by `gh api` is valid.
    if cli and subprocess.run([cli, 'auth', 'token', '--hostname', 'github.com'],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        return cli


def open_issues():
    route = f'repos/{repo}/issues?state=open&per_page=100'
    cli = authenticated_gh()
    if cli:
        output = subprocess.check_output(
            [cli, 'api', '--hostname', 'github.com', '--paginate', route],
            text=True,
        )
        decoder = json.JSONDecoder()
        index = 0
        # Older gh versions write one JSON array per page without a separator.
        while index < len(output):
            if output[index].isspace():
                index += 1
                continue
            page, index = decoder.raw_decode(output, index)
            yield from page
        return

    url = 'https://api.github.com/' + route
    while url:
        request = urllib.request.Request(url, headers={'User-Agent': 'rh-replay-tracker'})
        with urllib.request.urlopen(request, timeout=25) as response:
            yield from json.load(response)
            match = re.search(r'<([^>]+)>; rel="next"', response.headers.get('Link', ''))
            url = match[1] if match else None


def claims():
    cli = authenticated_gh()
    if cli:
        owner, name = repo.split('/')
        query = '''
        query($owner: String!, $name: String!, $endCursor: String) {
          repository(owner: $owner, name: $name) {
            issues(states: OPEN, first: 100, after: $endCursor) {
              nodes { title }
              pageInfo { hasNextPage endCursor }
            }
          }
        }
        '''
        pages = json.loads(subprocess.check_output(
            [cli, 'api', 'graphql', '--hostname', 'github.com', '--paginate', '--slurp',
             '-f', f'owner={owner}', '-f', f'name={name}', '-f', f'query={query}'],
            text=True))
        titles = (issue['title'] for page in pages
                  for issue in page['data']['repository']['issues']['nodes'])
    else:
        titles = (issue['title'] for issue in open_issues() if 'pull_request' not in issue)
    return {match[1] for title in titles if (match := re.fullmatch(r'Claim (M\d{6}|P\d{4})', title))}

TRACKED = ('modules.jsonl.gz', 'completed.tsv')
STALE_INDEX = ('tracker/modules.jsonl.gz or tracker/completed.tsv differs from main. '
               'Update the checkout (git pull --ff-only), then choose work again.')
UNVERIFIED_INDEX = 'Could not compare the tracker with main on GitHub. No claim was created; try again.'


def tracker_status():
    """Whether the local tracker files that decide claimability match main: 'ok', 'stale' or 'unknown'.

    The grant bot decides "already completed" from these two files on main, so a claim made from
    different copies is likely to conflict. The local id comes from `git hash-object`, which applies
    the checkout's line-ending conversion, so an unchanged file in a CRLF checkout matches its
    committed blob. A file that is absent both locally and on main matches. GitHub failures are
    'unknown' rather than 'stale'.
    """
    local = []
    for name in TRACKED:
        path = base / name
        if not path.exists():
            local.append(None)
            continue
        try:
            result = subprocess.run(['git', '-C', str(base), 'hash-object', '--', name],
                                    capture_output=True, text=True, check=True)
        except (OSError, subprocess.CalledProcessError):
            return 'stale'
        local.append(result.stdout.strip())
    owner, name = repo.split('/')
    fields = ' '.join(f'f{i}: object(expression: "main:tracker/{n}") {{ oid }}' for i, n in enumerate(TRACKED))
    query = 'query($owner: String!, $name: String!) { repository(owner: $owner, name: $name) { ' + fields + ' } }'
    try:
        data = json.loads(subprocess.check_output(
            ['gh', 'api', 'graphql', '--hostname', 'github.com',
             '-f', f'owner={owner}', '-f', f'name={name}', '-f', f'query={query}'],
            text=True, stderr=subprocess.DEVNULL))['data']['repository']
        remote = [(data[f'f{i}'] or {}).get('oid') for i in range(len(TRACKED))]
    except (OSError, subprocess.CalledProcessError, ValueError, KeyError, TypeError):
        return 'unknown'
    return 'ok' if remote == local else 'stale'


def run(targets,checkout,out,bundle,fast_bundle=False,*,project_modules=None):
 project=checkout.resolve();output=out.resolve()
 if output.exists():raise SystemExit('Output directory already exists: '+str(output))
 dirs=project.parent
 env={**os.environ,'ELAN_HOME':str(dirs/'elan'),'XDG_CACHE_HOME':str(dirs/'cache')}
 toolchain = (project / 'lean-toolchain').read_text().strip()
 if toolchain != 'leanprover/lean4:v4.33.1':raise SystemExit('Wrong Lean toolchain')
 launcher = ['elan', 'run', toolchain]
 version=subprocess.check_output([*launcher, 'lean','--version'],env=env,cwd=project,text=True).strip()
 mathlib=subprocess.check_output(['git','-C',str(project/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
 if '4.33.1' not in version or mathlib!=json.loads((base/'summary.json').read_text())['mathlib_commit']:raise SystemExit('Unexpected toolchain or mathlib')
 for r in targets:
  if digest(project/'src'/(r['module'].replace('.','/')+'.lean'))!=r['source_sha256']:raise SystemExit('Source hash mismatch: '+r['module'])
 cmd=['lake','build',*['+'+r['module']+':olean' for r in targets]]
 output.mkdir(parents=True,exist_ok=False)
 log=output/'build.log'
 build=project/'.lake/build'
 started=datetime.datetime.now(datetime.timezone.utc);clock=time.monotonic()
 with log.open('wb') as f:result=subprocess.run([*launcher, *cmd],cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
 elapsed=round(time.monotonic()-clock,1)
 if project_modules is None:project_modules={r['module'] for r in module_rows()}
 rebuilt=rebuilt_imports(log.read_text(errors='replace'),project_modules,{r['module'] for r in targets})
 receipt={'tasks':[r['id'] for r in targets],'started_utc':started.isoformat(),'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':elapsed,'host':host_resources(),'toolchain':version,'mathlib':mathlib,'inputs_manifest_sha256':digest(base.parent/'parts.sha256'),'command':cmd,'exit_code':result.returncode,'log_sha256':digest(log),'rebuilt_project_modules':rebuilt,'objects':{}}
 receipt['project_root']=str(project)
 if result.returncode==0:
  for r in targets:receipt['objects'][r['id']]=digest(build/'lib/lean'/(r['module'].replace('.','/')+'.olean'))
  if bundle or fast_bundle:
   artifact=output/'targets.tar.gz'
   options = {'compresslevel': 1} if fast_bundle else {}
   with tarfile.open(artifact,'w:gz',**options) as tar:
    for r in targets:
     stem=r['module'].replace('.','/')
     for prefix in ['lib/lean','ir']:
      path=build/prefix/stem
      for f in path.parent.glob(path.name+'.*'):
       # Lake regenerates this compiler input when building a module; it is
       # not an output artifact needed for reuse or downstream compilation.
       if f.name == path.name+'.setup.json':continue
       if f.is_file() and not f.is_symlink():tar.add(f,arcname=str(f.relative_to(build)),recursive=False)
   receipt['bundle_sha256']=digest(artifact)
 receipt_temp=output/'receipt.json.tmp'
 receipt_temp.write_text(json.dumps(receipt,indent=2)+'\n')
 receipt_temp.replace(output/'receipt.json')
 print('Saved',output,'with exit status',result.returncode)
 return result.returncode
def main():
 p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest='action',required=True)
 nx=s.add_parser('next');nx.add_argument('--limit',type=int,default=8)
 mode=nx.add_mutually_exclusive_group()
 mode.add_argument('--warm',type=Path,metavar='INVENTORY',help='rank disjoint builds against a worker inventory')
 nx.add_argument('--primary-inventory',type=Path,help='skip targets already on the primary')
 nx.add_argument('--max-builds',type=int,default=3,help='maximum estimated project modules per warm suggestion')
 mode.add_argument('--cold',action='store_true',help='show available individual modules with no project imports')
 nx.add_argument('--include-partial',action='store_true',help='also list partially completed packets (up to --limit more) whose open modules can be claimed individually')
 for n in ['show','claim','build']:
  sub=s.add_parser(n);sub.add_argument('target')
  if n=='build':
   sub.add_argument('checkout',type=Path);sub.add_argument('output',type=Path);sub.add_argument('--bundle',action='store_true')
   sub.add_argument('--fast-bundle',action='store_true',help='write the same tar members with gzip level 1 for faster packaging')
 a=p.parse_args()
 if a.action=='build':
  project_modules=set()
  targets=select(module_rows(),a.target,project_modules=project_modules)
  return run(targets,a.checkout,a.output,a.bundle,a.fast_bundle,project_modules=project_modules)
 rows=load()
 if a.action=='next':
  if a.primary_inventory and not a.warm:p.error('--primary-inventory requires --warm')
  if a.max_builds < 1:p.error('--max-builds must be positive')
  busy=claims()
  if a.warm:
   from replay_evidence import read_inventory
   from warm import suggestions
   cached=set(read_inventory(a.warm)['modules'])
   primary=set(read_inventory(a.primary_inventory)['modules']) if a.primary_inventory else set()
   for row,cost,consumers in suggestions(rows,busy,cached,primary,a.limit,a.max_builds):
    print(row['id'],row['packet'],'estimated project builds',cost,'direct consumers',consumers)
   return 0
  if a.cold:
   for row,sole,direct in cold_modules(rows,busy)[:max(0,a.limit)]:
    print(row['id'],row['packet'],row['module'],'sole-project-import consumers',sole,'direct consumers',direct)
   return 0
  full,partial=packet_suggestions(rows,busy,a.include_partial)
  for r,opened,total in full[:max(0,a.limit)]:
   print(r['packet'],'depth',r['depth'],'begins with',r['module'],f'{opened}/{total} open')
  shown_partial=partial[:max(0,a.limit)]
  for r,opened,total in shown_partial:
   print(r['packet'],'depth',r['depth'],'begins with',r['module'],f'{opened}/{total} open','(partial)')
  if shown_partial:
   print('Partial packets already have evidence for some modules and cannot be claimed as a packet.')
   print('Claim their open modules individually: show <packet> lists them, then claim <module ID>.')
  return 0
 sel=select(rows,a.target)
 if a.action=='show':
  for r in sel:print(json.dumps(r,ensure_ascii=False))
 elif a.action=='claim':
  busy=claims()
  if any(r['id'] in busy or r['packet'] in busy or r['state']!='open' for r in sel):raise SystemExit('One or more modules are already claimed, observed, or assigned.')
  status = tracker_status()
  if status != 'ok':
   raise SystemExit(STALE_INDEX if status == 'stale' else UNVERIFIED_INDEX)
  claim_id = a.target if a.target == sel[0]['packet'] else sel[0]['id']
  body = f'I am working on {claim_id}. I will attach the input hashes, build transcript and receipt, or close this claim if I stop.'
  subprocess.run(['gh', 'issue', 'create', '--repo', repo, '--title', 'Claim ' + claim_id,
                  '--body', body], check=True)
 return 0
if __name__=='__main__':sys.exit(main())
