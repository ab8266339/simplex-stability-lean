"""Regression checks for incomplete or malformed axiom-audit output."""
import sys, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audit_output import check_axiom_output

class AuditOutputTests(unittest.TestCase):
    def test_wrapped_expected_reports(self):
        text = "'A.x' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'A.y' depends on axioms: [Quot.sound]"
        self.assertTrue(check_axiom_output(text, ["A.x", "A.y"])["passed"])
    def test_explicit_axiom_free_report(self):
        self.assertTrue(check_axiom_output("'A.x' does not depend on any axioms", ["A.x"])["passed"])
    def test_empty_output_rejected(self):
        result = check_axiom_output("", ["A.x"])
        self.assertFalse(result["passed"])
        self.assertEqual(result["missing"], ["A.x"])
    def test_empty_request_rejected(self):
        self.assertFalse(check_axiom_output("", [])["passed"])
    def test_missing_report_rejected(self):
        self.assertFalse(check_axiom_output("'A.x' depends on axioms: [propext]", ["A.x", "A.y"])["passed"])
    def test_duplicate_report_rejected(self):
        line = "'A.x' depends on axioms: [propext]\n"
        self.assertFalse(check_axiom_output(line + line, ["A.x"])["passed"])
    def test_duplicate_request_rejected(self):
        self.assertFalse(check_axiom_output("'A.x' depends on axioms: [propext]", ["A.x", "A.x"])["passed"])
    def test_unexpected_name_rejected(self):
        self.assertFalse(check_axiom_output("'A.z' depends on axioms: [propext]", ["A.x"])["passed"])
    def test_unknown_axiom_rejected(self):
        self.assertFalse(check_axiom_output("'A.x' depends on axioms: [propext, sorryAx]", ["A.x"])["passed"])
    def test_truncated_report_rejected(self):
        self.assertFalse(check_axiom_output("'A.x' depends on axioms: [propext", ["A.x"])["passed"])
    def test_success_exit_text_without_reports_rejected(self):
        self.assertFalse(check_axiom_output("Build succeeded.\nAll targets completed.", ["A.x"])["passed"])

if __name__ == "__main__":
    unittest.main()
