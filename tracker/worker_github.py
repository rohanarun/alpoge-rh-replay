"""GitHub operations used by the replay dispatcher."""
import json
import subprocess

from submissions import gh_output, pages
import tasks


def api(route):
    return json.loads(gh_output(['gh', 'api', route]))


def post(route, method='POST', **fields):
    return json.loads(subprocess.check_output(
        ['gh', 'api', '--method', method, route, '--input', '-'], input=json.dumps(fields), text=True))


class GitHub:
    def __init__(self, fork):
        self.owner = api('user')['login']
        self.fork = api('repos/' + fork)['full_name']
        if self.fork.casefold() == tasks.repo.casefold():
            raise ValueError('Use your evidence repository for releases')
        self.issues = 'repos/' + tasks.repo + '/issues'

    def snapshot(self):
        return list(tasks.open_issues())

    def watch(self, numbers):
        # One read per group of outstanding reservations, including closed issues.
        owner, repo = tasks.repo.split('/')
        for offset in range(0, len(numbers), 40):
            fields = 'number title state author {login} labels(first:100){nodes{name}} comments{totalCount}'
            selections = ' '.join(f'i{n}:issue(number:{int(n)}){{{fields}}}' for n in numbers[offset:offset+40])
            query = 'query($owner:String!,$repo:String!){repository(owner:$owner,name:$repo){' + selections + '}}'
            data = json.loads(gh_output(['gh', 'api', 'graphql', '-f', 'query=' + query,
                                         '-f', 'owner=' + owner, '-f', 'repo=' + repo]))
            for issue in data['data']['repository'].values():
                if issue:
                    yield dict(number=issue['number'], title=issue['title'], state=issue['state'].lower(),
                               user=issue['author'] or {'login': ''}, labels=issue['labels']['nodes'],
                               comments=issue['comments']['totalCount'])

    def find_claim(self, marker):
        issues = pages(tasks.repo, 'issues?state=all&per_page=100&creator=' + self.owner)
        return next((i for i in issues if marker in (i.get('body') or '') and 'pull_request' not in i), None)

    def claim(self, target, marker):
        return post(self.issues, title='Claim ' + target,
                    body=f'I will attach the replay receipt and log or close this reservation.\n\n{marker}')

    def issue(self, number):
        return api(f'{self.issues}/{number}')

    def comments(self, number):
        return list(pages(tasks.repo, f'issues/{number}/comments?per_page=100'))

    def publish_assets(self, number, target, files):
        tag = f'replay-{target}-issue-{number}'
        route = f'repos/{self.fork}/releases/tags/{tag}'

        def release():
            return api(route)

        # Only an actual missing tag permits creation. A transport or auth failure
        # must leave the previous release alone.
        probe = subprocess.run(['gh', 'api', route], capture_output=True, text=True)
        if probe.returncode:
            if '(HTTP 404)' not in probe.stderr:
                raise RuntimeError(probe.stderr.strip())
            subprocess.run(['gh', 'release', 'create', tag, '--repo', self.fork, '--title', target,
                            '--notes', f'Replay evidence for {tasks.repo}#{number}.'], check=True)
            remote = release()
        else:
            remote = json.loads(probe.stdout)
        assets = {a['name']: a for a in remote['assets']}
        missing = [p for p in files if p.name not in assets]
        if missing:
            subprocess.run(['gh', 'release', 'upload', tag, '--repo', self.fork, *missing], check=True)
            assets = {a['name']: a for a in release()['assets']}
        links = []
        for path in files:
            asset = assets[path.name]
            if asset['state'] != 'uploaded' or asset.get('digest') != 'sha256:' + tasks.digest(path):
                raise ValueError('Published digest mismatch: ' + path.name)
            links.append(f"[{path.name}]({asset['browser_download_url']})")
        return ' · '.join(links)

    def submit(self, number, body):
        return post(f'{self.issues}/{number}/comments', body=body)['html_url']

    def close(self, number):
        post(f'{self.issues}/{number}', method='PATCH', state='closed', state_reason='not_planned')
