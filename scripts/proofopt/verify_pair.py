#!/usr/bin/env python3
"""Fork-only paired build runner. No automatic network calls in plan mode.
Run only on a trusted, adequately provisioned Linux machine; Lean executes code.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import subprocess
import time

PROOF = 'src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean'
PROTECTED = ('src/Challenge.lean', 'comparator.json', 'export-targets.txt',
             'comparator/FormalConjecturesChallenge.lean', 'comparator/formal-conjectures.json',
             'comparator/formal-conjectures-export-targets.txt', 'src/Main.lean',
             'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
SHA = re.compile(r'[0-9a-f]{40}')


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args]).decode().strip()


def plan(repo, base, candidate):
    for ref in (base, candidate):
        if not SHA.fullmatch(ref) or git(repo, 'rev-parse', ref + '^{commit}') != ref:
            raise ValueError('use full, existing commit IDs')
    if git(repo, 'merge-base', base, candidate) != base:
        raise ValueError('candidate is not based on fixed baseline')
    paths = git(repo, 'diff', '--name-only', '--no-renames', '-z', base, candidate).split('\0')
    if paths != [PROOF, '']:
        raise ValueError('candidate must change exactly the approved proof file')
    identities = {}
    for path in PROTECTED:
        before = git(repo, 'rev-parse', base + ':' + path)
        after = git(repo, 'rev-parse', candidate + ':' + path)
        if before != after:
            raise ValueError('protected file changed: ' + path)
        identities[path] = before
    return {'base': base, 'candidate': candidate, 'changed_path': PROOF,
            'protected_blobs': identities, 'before_blob': git(repo, 'rev-parse', base + ':' + PROOF),
            'after_blob': git(repo, 'rev-parse', candidate + ':' + PROOF),
            'lean_toolchain': git(repo, 'show', base + ':lean-toolchain'),
            'mathlib': next(p['rev'] for p in json.loads(git(repo, 'show', base + ':lake-manifest.json'))['packages'] if p['name'] == 'mathlib')}


def run(repo, out, base, candidate, mode, jobs):
    repo, out = Path(repo).resolve(), Path(out).resolve()
    if mode not in ('incremental', 'clean', 'comparator') or jobs < 1:
        raise ValueError('invalid run mode/jobs')
    if out.exists() or out.is_relative_to(repo):
        raise ValueError('use a new output directory outside the source checkout')
    spec = plan(repo, base, candidate)
    if not shutil.which('lake'):
        raise RuntimeError('lake unavailable')
    if mode == 'comparator' and not shutil.which('bwrap'):
        raise RuntimeError('bubblewrap unavailable')
    out.mkdir(parents=True)
    env = os.environ.copy()
    for key in ('LAKE_ARTIFACT_CACHE', 'MATHLIB_CACHE_GET_URL', 'LEAN_NUM_THREADS'):
        env.pop(key, None)
    env.update(LEAN_ABORT_ON_PANIC='1', LEAN_NUM_THREADS=str(jobs))
    if mode != 'incremental':
        env.update(LAKE_ARTIFACT_CACHE='false', MATHLIB_CACHE_GET_URL='https://cache.mathlib.org/mathlib4')
    record = {'schema': 1, 'plan': spec, 'mode': mode, 'jobs': jobs,
              'environment': {'platform': platform.platform(), 'machine': platform.machine(),
                              'cpu_count': os.cpu_count(), 'lake': shutil.which('lake'),
                              'cache_policy': 'project-cache' if mode == 'incremental' else 'mathlib-only',
                              'free_disk_bytes': shutil.disk_usage(out).free},
              'steps': [], 'status': 'running', 'build_cpu_reduction': None,
              'independent_verification': False}
    def save():
        tmp = out / 'report.tmp'
        tmp.write_text(json.dumps(record, indent=2) + '\n')
        tmp.replace(out / 'report.json')
    def step(label, cwd, command):
        log = out / (label + '.log')
        t = time.monotonic()
        a = resource.getrusage(resource.RUSAGE_CHILDREN)
        with log.open('w') as f:
            p = subprocess.run(command, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
        b = resource.getrusage(resource.RUSAGE_CHILDREN)
        row = {'label': label, 'command': command, 'exit': p.returncode,
               'wall_seconds': time.monotonic()-t, 'user_seconds': b.ru_utime-a.ru_utime,
               'system_seconds': b.ru_stime-a.ru_stime, 'log': log.name}
        record['steps'].append(row)
        save()
        if p.returncode:
            raise RuntimeError(label + ' failed, see ' + str(log))
        return row
    def checkout(label, ref):
        path = out / label
        step(label+'-checkout', repo, ['git', 'worktree', 'add', '--detach', str(path), ref])
        if git(path, 'rev-parse', 'HEAD') != ref:
            raise RuntimeError('unexpected worktree commit')
        return path
    def assert_clean(path, ref):
        if git(path, 'rev-parse', 'HEAD') != ref or git(path, 'status', '--porcelain', '--untracked-files=no'):
            raise RuntimeError('tracked checkout changed during validation')
    try:
        save()
        if mode == 'incremental':
            w = checkout('incremental', base)
            step('toolchain', w, ['lake', 'env', 'lean', '--version'])
            step('baseline-cache', w, ['lake', 'exe', 'cache', 'get'])
            step('baseline-cache-check', w, ['lake', 'build', '--no-build'])
            assert_clean(w, base)
            step('switch-candidate', w, ['git', 'checkout', '--detach', candidate])
            assert_clean(w, candidate)
            step('candidate-build', w, ['lake', 'build'])
            assert_clean(w, candidate)
        else:
            builds = []
            for label, ref in [('baseline', base), ('candidate', candidate)]:
                w = checkout(label, ref)
                if (w / '.lake' / 'build').exists():
                    raise RuntimeError('fresh proof build directory required')
                step(label+'-toolchain', w, ['lake', 'env', 'lean', '--version'])
                step(label+'-mathlib-cache', w, ['lake', 'exe', 'mathlib/cache', 'get'])
                assert_clean(w, ref)
                if (w / '.lake' / 'build').exists():
                    raise RuntimeError('proof build directory populated during cache setup')
                cmd = ['lake', 'build'] if mode == 'clean' else ['lake', 'comparator']
                builds.append(step(label+'-validate', w, cmd))
                assert_clean(w, ref)
            if mode == 'clean':
                cpu = [r['user_seconds']+r['system_seconds'] for r in builds]
                if cpu[0] <= 0:
                    raise RuntimeError('invalid baseline CPU measurement')
                record['build_cpu_reduction'] = 1-cpu[1]/cpu[0]
            else:
                record['independent_verification'] = True
        record['status'] = 'passed'
    except BaseException as e:
        record['status'] = 'failed'
        record['error'] = str(e)
        raise
    finally:
        save()
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['plan', 'incremental', 'clean', 'comparator'])
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--base', required=True)
    p.add_argument('--candidate', required=True)
    p.add_argument('--out', type=Path)
    p.add_argument('--jobs', type=int, default=4)
    a = p.parse_args()
    if a.mode == 'plan':
        print(json.dumps(plan(a.repo, a.base, a.candidate), indent=2))
    else:
        if a.out is None:
            p.error('--out required for execution')
        run(a.repo, a.out, a.base, a.candidate, a.mode, a.jobs)


if __name__ == '__main__':
    main()
