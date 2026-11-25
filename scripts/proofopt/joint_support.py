#!/usr/bin/env python3
"""Exact budgeted planning for an all-supports-removed dependency model.

The model is not a Lean kernel reachability oracle. Field-reach associations are
historical candidate evidence, not sufficient conditions for legal removal.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path


def read_field_reach(raw):
    groups, supports, seen = set(), defaultdict(set), set()
    for lineno, line in enumerate(raw.decode('utf-8').splitlines(), 1):
        parts = line.split('\t')
        if len(parts) != 4:
            raise ValueError(f'line {lineno}: expected four TSV columns')
        group, field, count, names = parts
        constants = set(names.split(';')) if names else set()
        if not group or not field or '' in constants or int(count) != len(constants):
            raise ValueError(f'line {lineno}: invalid field or count')
        if (group, field) in seen:
            raise ValueError(f'line {lineno}: duplicate field')
        seen.add((group, field))
        groups.add(group)
        for c in constants:
            supports[c].add(group)
    return groups, Counter(frozenset(s) for s in supports.values()), len(seen)


def read_fixture(data):
    # Lossless (up to candidate renaming) compression of weighted support sets.
    groups, edges = set(), Counter()
    blocks = [(1, [[1, int(w)]] if int(w) else [])
              for w, count in data['singletons'].items() for _ in range(count)]
    blocks += data['multi']
    for i, (n, entries) in enumerate(blocks):
        names = [f'{i:04d}.{j:02d}' for j in range(n)]
        groups.update(names)
        for mask, weight in entries:
            if not 0 < mask < (1 << n) or weight <= 0:
                raise ValueError('invalid fixture mask/weight')
            edges[frozenset(name for j, name in enumerate(names) if mask >> j & 1)] += weight
    return groups, edges


def components(groups, edges):
    parent = {g: g for g in groups}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for s, w in edges.items():
        if not s or not s <= groups or type(w) is not int or w <= 0:
            raise ValueError('invalid support set or weight')
        members = sorted(s)
        for x in members[1:]:
            parent[find(x)] = find(members[0])
    blocks, weights = defaultdict(list), defaultdict(Counter)
    for g in sorted(groups):
        blocks[find(g)].append(g)
    for s, w in edges.items():
        weights[find(min(s))][s] += w
    return sorted([(names, weights[root]) for root, names in blocks.items()])


def local_frontier(names, edges, cap):
    n = len(names)
    if n > cap:
        raise ValueError(f'component size {n} exceeds exact-search cap {cap}')
    index = {g: i for i, g in enumerate(names)}
    f = [0] * (1 << n)
    for s, w in edges.items():
        f[sum(1 << index[g] for g in s)] += w
    # Subset zeta transform: f[S] = sum_{T subset S} w[T].
    for i in range(n):
        bit = 1 << i
        for m in range(1 << n):
            if m & bit:
                f[m] += f[m ^ bit]
    best = [-1] * (n + 1)
    masks = [0] * (n + 1)
    for m, value in enumerate(f):
        k = m.bit_count()
        if value > best[k]:
            best[k], masks[k] = value, m
    return best, masks


def solve(groups, edges, budget, cap=20):
    if not 0 <= budget <= len(groups) or not 1 <= cap <= 22:
        raise ValueError('invalid budget or component cap')
    blocks = components(groups, edges)
    # Exact-cardinality max-plus convolution; store choices for reconstruction.
    dp, history, local, evaluated = [0], [], [], 0
    for names, weights in blocks:
        vals, masks = local_frontier(names, weights, cap)
        evaluated += 1 << len(names)
        nxt = [-1] * (len(dp) + len(names))
        choice = [0] * len(nxt)
        for i, old in enumerate(dp):
            for j, value in enumerate(vals):
                if old + value > nxt[i+j]:
                    nxt[i+j], choice[i+j] = old + value, j
        dp = nxt
        history.append(choice)
        local.append((names, masks))
    k, selected = budget, set()
    for choice, (names, masks) in reversed(list(zip(history, local))):
        j = choice[k]
        selected.update(g for i, g in enumerate(names) if masks[j] >> i & 1)
        k -= j
    assert k == 0 and len(selected) == budget
    assert sum(w for s, w in edges.items() if s <= selected) == dp[budget]
    return {'optimal': dp, 'budget': budget, 'selected': sorted(selected),
            'selected_gain': dp[budget], 'component_count': len(blocks),
            'component_histogram': dict(sorted(Counter(len(b[0]) for b in blocks).items())),
            'local_subsets_evaluated': evaluated, 'groups': len(groups),
            'support_sets': len(edges), 'total_weight': sum(edges.values())}


def greedy_curve(groups, edges):
    incident = defaultdict(list)
    unmet = {s: len(s) for s in edges}
    for s in edges:
        for g in s:
            incident[g].append(s)
    remaining, out = set(groups), [0]
    while remaining:
        g = min(remaining, key=lambda x: (-sum(edges[s] for s in incident[x]
                                                if unmet[s] == 1), x))
        out.append(out[-1] + sum(edges[s] for s in incident[g] if unmet[s] == 1))
        remaining.remove(g)
        for s in incident[g]:
            unmet[s] -= 1
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument('--field-reach', type=Path)
    src.add_argument('--fixture', type=Path)
    p.add_argument('--expect-blob')
    p.add_argument('--budget', type=int, required=True)
    p.add_argument('--max-component', type=int, default=20)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    raw = (args.field_reach or args.fixture).read_bytes()
    blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
    if args.expect_blob and blob != args.expect_blob:
        p.error(f'Git blob mismatch: {blob}')
    if args.field_reach:
        groups, edges, rows = read_field_reach(raw)
    else:
        groups, edges = read_fixture(json.loads(raw))
        rows = None
    report = solve(groups, edges, args.budget, args.max_component)
    greedy = greedy_curve(groups, edges)
    report.update(schema=1, input_blob=blob, rows=rows, greedy=greedy,
                  model='all historical support associations must be selected; not kernel reachability')
    report['max_greedy_gap'] = max(a-b for a,b in zip(report['optimal'], greedy))
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
