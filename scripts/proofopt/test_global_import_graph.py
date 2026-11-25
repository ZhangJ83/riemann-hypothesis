"""Unit tests for the ProofOpt source-level global import graph analyzer."""
import unittest

from global_import_graph import ImportGraph, make_report, parse_lean_file


class GlobalImportGraphTests(unittest.TestCase):
    def test_clump_headers_preserve_original_module_imports(self):
        source = """module

public import A.B
import C.D

-- This file was produced by scripts/clump.py
-- ===== clump member: X.Y =====
-- clump-header: {"m":"X.Y","h":"module\\n\\npublic import A.B\\nimport Z.Q\\n"}
section
theorem foo : True := by trivial
end -- clump:auto
-- ===== end clump member: X.Y =====
"""
        parsed = parse_lean_file(source)
        self.assertEqual(parsed["imports"], ["A.B", "C.D"])
        self.assertEqual(parsed["members"], [{"module": "X.Y", "imports": ["A.B", "Z.Q"]}])

    def test_root_closure_and_shared_dependency(self):
        graph = ImportGraph()
        for name, deps in [("R1", ["S", "A"]), ("R2", ["S", "B"]),
                           ("S", []), ("A", []), ("B", [])]:
            graph.add_file(name, name + ".lean",
                           {"imports": deps, "members": [], "is_clump": False})
        graph.finalize()
        self.assertEqual(graph.internal_closure(["R1"]), {"R1", "S", "A"})
        shared = graph.shared_dependency_report(["R1", "R2"])
        self.assertEqual(shared[0]["module"], "S")
        self.assertEqual(shared[0]["root_count"], 2)
        self.assertEqual(make_report(graph, ["R1", "R2"])["union_closure_count"], 5)

    def test_cycles_are_reported(self):
        graph = ImportGraph()
        graph.add_file("A", "A.lean", {"imports": ["B"], "members": [], "is_clump": False})
        graph.add_file("B", "B.lean", {"imports": ["A"], "members": [], "is_clump": False})
        graph.finalize()
        self.assertEqual(graph.cycles(), [["A", "B"]])


if __name__ == "__main__":
    unittest.main()
