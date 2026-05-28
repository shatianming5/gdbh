import unittest

from audit_lean_axioms import (
    ALLOWED_AXIOMS,
    iter_axiom_output_lines,
    parse_axiom_line,
    render_lean_probe,
)


class LeanAxiomAuditParserTests(unittest.TestCase):
    def test_parse_axiom_line(self) -> None:
        theorem, axioms = parse_axiom_line(
            "'Gdbh.example' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]"
        )

        self.assertEqual(theorem, "Gdbh.example")
        self.assertEqual(axioms, ALLOWED_AXIOMS)

    def test_parse_empty_axiom_line(self) -> None:
        theorem, axioms = parse_axiom_line("'Gdbh.example' depends on axioms: []")

        self.assertEqual(theorem, "Gdbh.example")
        self.assertEqual(axioms, set())

    def test_iter_axiom_output_lines_joins_wrapped_output(self) -> None:
        output = (
            "'Gdbh.long_theorem_name' depends on axioms: [propext,\n"
            " Classical.choice, Quot.sound]\n"
        )

        self.assertEqual(
            iter_axiom_output_lines(output),
            [
                "'Gdbh.long_theorem_name' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]"
            ],
        )

    def test_render_lean_probe_imports_project(self) -> None:
        probe = render_lean_probe(["Gdbh.example"])

        self.assertIn("import Gdbh", probe)
        self.assertIn("#print axioms Gdbh.example", probe)


if __name__ == "__main__":
    unittest.main()
