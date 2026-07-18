import json
from pathlib import Path
from unittest import TestCase, main

from check_axiom_audit import expected_declarations, printed_axioms, validate_audit


SOURCE = """
#print axioms WeakSimplex.first
#print axioms
  WeakSimplex.second
"""
AUDIT_FILE = Path("Audit.lean")
REQUIRED = frozenset({"WeakSimplex.first", "WeakSimplex.second"})
STANDARD = ("propext", "Classical.choice", "Quot.sound")


def diagnostic(
    declaration: str,
    *,
    axioms: tuple[str, ...] = STANDARD,
    line: int,
    file_name: str = "Audit.lean",
) -> str:
    return json.dumps(
        {
            "data": f"'{declaration}' depends on axioms: [{', '.join(axioms)}]",
            "fileName": file_name,
            "pos": {"line": line, "column": 0},
            "severity": "information",
        }
    )


def validate(source: str, output: str) -> list[str]:
    return validate_audit(source, output, AUDIT_FILE, REQUIRED)


class AxiomAuditTests(TestCase):
    def test_parses_multiline_source_and_json_output(self) -> None:
        output = "\n".join(
            [
                diagnostic("WeakSimplex.first", line=2),
                diagnostic("WeakSimplex.second", line=3),
            ]
        )
        self.assertEqual(
            expected_declarations(SOURCE), ["WeakSimplex.first", "WeakSimplex.second"]
        )
        self.assertEqual(len(printed_axioms(output)), 2)
        self.assertEqual(validate(SOURCE, output), [])

    def test_rejects_unexpected_axiom(self) -> None:
        output = "\n".join(
            [
                diagnostic(
                    "WeakSimplex.first", axioms=STANDARD + ("sorryAx",), line=2
                ),
                diagnostic("WeakSimplex.second", line=3),
            ]
        )
        findings = validate(SOURCE, output)
        self.assertTrue(any("WeakSimplex.first" in finding for finding in findings))

    def test_rejects_missing_report(self) -> None:
        findings = validate(SOURCE, diagnostic("WeakSimplex.first", line=2))
        self.assertTrue(any("WeakSimplex.second" in finding for finding in findings))
        self.assertTrue(any("expected 2" in finding for finding in findings))

    def test_rejects_extra_and_duplicate_reports(self) -> None:
        output = "\n".join(
            [
                diagnostic("WeakSimplex.first", line=2),
                diagnostic("WeakSimplex.first", line=2),
                diagnostic("WeakSimplex.second", line=3),
                diagnostic("WeakSimplex.extra", line=4),
            ]
        )
        findings = validate(SOURCE, output)
        self.assertTrue(any("duplicate" in finding for finding in findings))
        self.assertTrue(any("WeakSimplex.extra" in finding for finding in findings))

    def test_rejects_duplicate_source_declaration(self) -> None:
        source = SOURCE + "#print axioms WeakSimplex.first\n"
        findings = validate(source, "")
        self.assertTrue(any("audit source contains duplicate" in finding for finding in findings))

    def test_rejects_duplicate_axiom_tokens(self) -> None:
        output = "\n".join(
            [
                diagnostic(
                    "WeakSimplex.first", axioms=STANDARD + ("Quot.sound",), line=2
                ),
                diagnostic("WeakSimplex.second", line=3),
            ]
        )
        findings = validate(SOURCE, output)
        self.assertTrue(any("duplicate axiom tokens" in finding for finding in findings))

    def test_rejects_wrong_source_position(self) -> None:
        output = "\n".join(
            [
                diagnostic("WeakSimplex.first", line=99),
                diagnostic("WeakSimplex.second", line=3),
            ]
        )
        findings = validate(SOURCE, output)
        self.assertTrue(any("does not match #print" in finding for finding in findings))

    def test_rejects_plaintext_spoof(self) -> None:
        output = """
'WeakSimplex.first' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakSimplex.second' depends on axioms: [propext, Classical.choice, Quot.sound]
"""
        findings = validate(SOURCE, output)
        self.assertTrue(any("not a JSON diagnostic" in finding for finding in findings))

    def test_rejects_commented_commands_as_coverage(self) -> None:
        source = "-- #print axioms WeakSimplex.first\n"
        findings = validate_audit(
            source,
            "",
            AUDIT_FILE,
            frozenset({"WeakSimplex.first"}),
        )
        self.assertEqual(expected_declarations(source), [])
        self.assertTrue(any("required declarations absent" in finding for finding in findings))

    def test_rejects_empty_dossier(self) -> None:
        self.assertTrue(validate_audit("-- no commands", "", AUDIT_FILE, frozenset()))


if __name__ == "__main__":
    main()
