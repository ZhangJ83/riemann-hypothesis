import itertools
import json
import random
import subprocess
import sys
import unittest
from collections import Counter
from pathlib import Path

from joint_support import components, greedy_curve, read_field_reach, read_fixture, solve

HERE = Path(__file__).parent


class JointSupportTests(unittest.TestCase):
    def test_parser_union_not_sum(self):
        groups, edges, rows = read_field_reach(b'A\tf\t2\tx;y\nA\tg\t1\tx\nB\th\t1\tx\nC\ti\t0\t\n')
        self.assertEqual(groups, {'A','B','C'})
        self.assertEqual(edges, {frozenset('AB'): 1, frozenset('A'): 1})
        self.assertEqual(rows, 4)

    def test_bad_count(self):
        with self.assertRaises(ValueError):
            read_field_reach(b'A\tf\t2\tx\n')

    def test_duplicate_field(self):
        with self.assertRaises(ValueError):
            read_field_reach(b'A\tf\t1\tx\nA\tf\t1\ty\n')

    def test_empty_support_rejected(self):
        with self.assertRaises(ValueError):
            solve({'A'}, {frozenset(): 1}, 1)

    def test_unknown_support_rejected(self):
        with self.assertRaises(ValueError):
            solve({'A'}, {frozenset('B'): 1}, 1)

    def test_invalid_budget(self):
        with self.assertRaises(ValueError):
            solve({'A'}, {}, 2)

    def test_component_cap(self):
        with self.assertRaises(ValueError):
            solve(set('ABC'), {frozenset('ABC'): 1}, 2, cap=2)

    def test_empty_problem(self):
        self.assertEqual(solve(set(), {}, 0)['optimal'], [0])

    def test_joint_gain_beats_greedy(self):
        edges = {frozenset('A'): 3, frozenset('B'): 1, frozenset('C'): 1, frozenset('BC'): 9}
        result = solve(set('ABC'), edges, 2)
        self.assertEqual(result['selected'], ['B','C'])
        self.assertEqual(result['selected_gain'], 11)
        self.assertEqual(greedy_curve(set('ABC'), edges)[2], 4)

    def test_randomized_exhaustive_oracle(self):
        rng = random.Random(1042)
        for n in range(1, 10):
            for _ in range(16):
                names = set(range(n))
                edges = Counter()
                for _ in range(15):
                    s = frozenset(rng.sample(range(n), rng.randint(1, n)))
                    edges[s] += rng.randint(1, 10)
                expected = [max(sum(w for s,w in edges.items() if s <= set(c))
                                for c in itertools.combinations(range(n), k))
                            for k in range(n+1)]
                result = solve(names, edges, rng.randrange(n+1))
                self.assertEqual(result['optimal'], expected)

    def test_historical_full_weighted_fixture(self):
        groups, edges = read_fixture(json.loads((HERE/'historical_fixture.json').read_text()))
        result = solve(groups, edges, 232)
        self.assertEqual(result['groups'], 862)
        self.assertEqual(result['total_weight'], 4062)
        self.assertEqual(result['component_count'], 760)
        self.assertEqual(result['local_subsets_evaluated'], 22528)
        self.assertEqual(result['selected_gain'], 3605)
        for k,v in {0:0,10:1200,20:1607,30:1887,50:2273,100:2868,200:3487,
                    300:3790,400:3950,500:4050,516:4062,862:4062}.items():
            self.assertEqual(result['optimal'][k], v)

    def test_cli_json(self):
        output = subprocess.check_output([sys.executable, str(HERE/'joint_support.py'),
                                          '--fixture', str(HERE/'historical_fixture.json'),
                                          '--budget', '2'], text=True)
        self.assertEqual(json.loads(output)['selected_gain'], 423)


if __name__ == '__main__':
    unittest.main()
