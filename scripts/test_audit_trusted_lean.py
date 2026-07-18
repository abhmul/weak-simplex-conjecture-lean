from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase, main

from audit_trusted_lean import audit_file, code_tokens, mask_comments_and_literals


class MaskingTests(TestCase):
    def test_masks_nested_comments_chars_and_preserves_normal_string_text(self) -> None:
        source = '''
/- outer /- axiom nested : False -/ unsafe -/
def message := "sorry admit"
def quote := '"'
def «unsafe» := 0
def safe := 0
'''
        code = mask_comments_and_literals(source)
        self.assertNotIn("axiom", code)
        self.assertIn("sorry admit", code)
        self.assertTrue(
            any(token.value == "unsafe" and token.is_escaped for token in code_tokens(code))
        )
        self.assertIn("def safe", code)


class AuditTests(TestCase):
    def audit(self, relative_path: str, source: str) -> list[str]:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / relative_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            public_root = root / "WeakSimplexConjectureLean.lean"
            return audit_file(path, public_root)

    def test_rejects_forbidden_tokens_after_comments_and_modifiers(self) -> None:
        source = '''
/-- documentation -/ private axiom hidden : False
/- documentation -/ public unsafe def run : Nat := 0
def incomplete : Nat := by sorry
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/Bad.lean", source)
        self.assertEqual(len(findings), 3)
        self.assertTrue(any("'axiom'" in finding for finding in findings))
        self.assertTrue(any("'unsafe'" in finding for finding in findings))
        self.assertTrue(any("'sorry'" in finding for finding in findings))

    def test_masks_comments_but_exposes_forbidden_normal_string_words(self) -> None:
        source = '''
/- axiom fake : False -/
def explanation := "unsafe sorry admit"
def safe := 0
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/StringWords.lean", source)
        self.assertEqual(len(findings), 3)
        self.assertTrue(any("'unsafe'" in finding for finding in findings))
        self.assertTrue(any("'sorry'" in finding for finding in findings))
        self.assertTrue(any("'admit'" in finding for finding in findings))

    def test_rejects_native_decide_in_interpolation_holes(self) -> None:
        source = '''
def explicit := s!"{(let _h : True := (by native_decide); 0)}"
def bare : Lean.Elab.Term.TermElabM Unit := do
  throwError "{(let _h : True := (by native_decide); (0 : Nat))}"
def spaced : Lean.MessageData := m! "{(let _h : True := (by native_decide); (0 : Nat))}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/Interpolation.lean", source)
        self.assertEqual(len(findings), 3)
        self.assertTrue(all("'native_decide'" in finding for finding in findings))

    def test_masks_interpolation_literals_comments_and_safe_identifiers(self) -> None:
        source = r'''
def native_decider := 0
def «native_decider» := 0
def ordinary := "ordinary prose"
def literal := s!"literal \{still literal}"
def commented := s!"{
  -- harmless } " comment
  /- harmless outer } " comment /- nested } " comment -/ -/
  0
}"
def escaped := s!"{«native_decider»}"
def similar := s!"{native_decider}"
def nestedString := s!"{"nested prose"}"
def character := s!"{'{'}"
def nestedRaw := s!"{r#"raw " quote"#}"
'''
        self.assertEqual(self.audit("WeakSimplexConjectureLean/Core/Benign.lean", source), [])

    def test_conservatively_rejects_unescaped_brace_group_in_ordinary_string(self) -> None:
        source = 'def conservative := "{native_decide}"\n'
        findings = self.audit("WeakSimplexConjectureLean/Core/Conservative.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_unmatched_ordinary_brace_does_not_hide_following_code(self) -> None:
        source = '''
def x : String := "{"
axiom hidden : False
def rejected : True := by native_decide
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/UnmatchedBrace.lean", source)
        self.assertEqual(len(findings), 2)
        self.assertTrue(any("'axiom'" in finding for finding in findings))
        self.assertTrue(any("'native_decide'" in finding for finding in findings))

    def test_interpolation_code_after_nested_ordinary_strings_remains_visible(self) -> None:
        source = '''
def nested := s!"{(let first := "alpha"; let second := "beta";
  let _h : True := (by native_decide); first ++ second)}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/NestedOrdinary.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_rejects_forbidden_spellings_in_no_brace_ordinary_string(self) -> None:
        source = 'def prose := "axiom native_decide unsafe sorry admit"\n'
        findings = self.audit("WeakSimplexConjectureLean/Core/Prose.lean", source)
        self.assertEqual(len(findings), 5)
        for keyword in ("axiom", "native_decide", "unsafe", "sorry", "admit"):
            self.assertTrue(any(f"'{keyword}'" in finding for finding in findings))

    def test_escaped_close_identifier_does_not_desynchronize_interpolation(self) -> None:
        source = '''
def «}» := 0
def x := s!"{(let _ := «}»
  let _h : True := by native_decide
  (0 : Nat))}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/EscapedDelimiters.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_quote_and_comment_delimiters_inside_escaped_identifiers_are_skipped(self) -> None:
        source = '''
def escapedDelimiters : String := s!"{(
  let «"» := 1
  let «/-» := 2
  let _h : True := (by native_decide)
  «"» + «/-»
)}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/OtherEscaped.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_numeral_adjacent_raw_string_does_not_hide_following_code(self) -> None:
        source = '''
syntax "drop" num term : term
macro "drop" _n:num _t:term : term => `(0)
def x := drop 1r#"embedded " literal"#
axiom hidden : False
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/AdjacentRaw.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'axiom'", findings[0])

    def test_custom_literal_close_brace_does_not_hide_interpolation_code(self) -> None:
        source = '''
syntax "swallow" "}" term : term
macro "swallow" "}" t:term : term => pure t
def x := s!"{swallow } (let _h : True := by native_decide
  (0 : Nat))}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/CustomClose.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_rejects_reparsed_term_hidden_in_raw_string(self) -> None:
        source = '''
import Lean

open Lean Elab Term

syntax:max "rawTerm% " str : term

elab_rules : term
  | `(rawTerm% $value:str) => do
      let some input := value.raw.isStrLit? | throwUnsupportedSyntax
      let parsed ←
        match Parser.runParserCategory (← getEnv) `term input with
        | .ok stx => pure stx
        | .error message => throwError message
      elabTerm parsed none

def replayed : True := rawTerm% r#"show True from by native_decide"#
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/RawReparse.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_scientific_literal_does_not_fuse_following_tactic_identifier(self) -> None:
        source = '''
syntax "useSci" scientific tacticSeq : term
macro "useSci" _n:scientific t:tacticSeq : term => `(by $t)
theorem bypass : True := useSci 1e2native_decide
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/ScientificFusion.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_character_literal_does_not_fuse_following_tactic_identifier(self) -> None:
        source = '''
syntax "useChar" char tacticSeq : term
macro "useChar" _c:char t:tacticSeq : term => `(by $t)
theorem bypass : True := useChar 'x'native_decide
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/CharFusion.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_underscored_and_hex_literals_do_not_fuse_following_tactics(self) -> None:
        source = '''
syntax "useNum" num tacticSeq : term
macro "useNum" _n:num t:tacticSeq : term => `(by $t)
theorem bypassUnderscore : True := useNum 1_000native_decide
theorem bypassHex : True := useNum 0xDEADnative_decide
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/NumberFusion.lean", source)
        self.assertEqual(len(findings), 2)
        self.assertTrue(all("'native_decide'" in finding for finding in findings))

    def test_rejects_native_decide_in_nested_interpolation_and_braces(self) -> None:
        source = '''
def nested := s!"outer {{
  value := s!"inner {(let _h : True := (by native_decide); 0)}"
}}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/Nested.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_raw_strings_do_not_mask_following_code(self) -> None:
        source = '''
def zeroHashes := r"{ordinary}"
def partialDelimiter := r##"ordinary "# remains literal"##
def exactExploit := r#"embedded " literal"#
axiom hidden : False
def rejected : True := by native_decide
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/RawStrings.lean", source)
        self.assertEqual(len(findings), 2)
        self.assertTrue(any("'axiom'" in finding for finding in findings))
        self.assertTrue(any("'native_decide'" in finding for finding in findings))

    def test_nested_literals_do_not_hide_following_interpolation_code(self) -> None:
        source = '''
def nestedLiterals := s!"{
  let raw := r#"raw " } remains literal"#
  let ordinary := "ordinary }"
  let character := '}'
  let _h : True := (by native_decide)
  0
}"
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/NestedLiterals.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'native_decide'", findings[0])

    def test_respects_unicode_boundaries_but_rejects_escaped_forbidden_name(self) -> None:
        source = "def αunsafe := 0\ndef unsafeβ := 0\ndef unsafe! := 0\ndef «unsafe» := 0\n"
        findings = self.audit("WeakSimplexConjectureLean/Core/Unicode.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("'unsafe'", findings[0])

    def test_rejects_direct_sorry_axiom_references(self) -> None:
        source = (
            "def bad : False := sorryAx False true\n"
            "def escaped : False := «sorryAx» False true\n"
        )
        findings = self.audit("WeakSimplexConjectureLean/Core/SorryAx.lean", source)
        self.assertEqual(len(findings), 2)
        self.assertTrue(all("'sorryAx'" in finding for finding in findings))

    def test_rejects_public_import_of_scaffold_from_production(self) -> None:
        source = '''
module
/-- documentation -/ public meta import all
  WeakSimplexConjectureLean.«Scaffold».Assumption
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/BadImport.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("imports Scratch or Scaffold", findings[0])

    def test_allows_internal_scaffold_import(self) -> None:
        source = "import WeakSimplexConjectureLean.Scaffold.Other\n"
        self.assertEqual(
            self.audit("WeakSimplexConjectureLean/Scaffold/Assumption.lean", source), []
        )

    def test_rejects_scratch_import_from_vendor(self) -> None:
        source = "import WeakSimplexConjectureLean.Scratch.Experiment\n"
        findings = self.audit("WeakSimplexConjectureLean/Vendor/External.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("imports Scratch or Scaffold", findings[0])

    def test_rejects_native_decide_and_root_nonproduction_imports(self) -> None:
        source = '''
import Scratch.Experiment
import «Scaffold».Assumption
def rejected : True := by native_decide
def escaped := «native_decide»
'''
        findings = self.audit("WeakSimplexConjectureLean/Core/CombinedProbe.lean", source)
        token_findings = [finding for finding in findings if "forbidden Lean token" in finding]
        import_findings = [finding for finding in findings if "imports Scratch" in finding]
        self.assertEqual(len(findings), 4)
        self.assertEqual(len(token_findings), 2)
        self.assertTrue(all("'native_decide'" in finding for finding in token_findings))
        self.assertEqual(len(import_findings), 2)

    def test_allows_root_nonproduction_import_from_nonproduction_path(self) -> None:
        source = "import Scratch.Helper\nimport Scaffold.Other\n"
        self.assertEqual(self.audit("Scratch/Internal.lean", source), [])

    def test_absolute_nonproduction_ancestor_does_not_exempt_production_path(self) -> None:
        for ancestor in ("Scratch", "Scaffold"):
            with self.subTest(ancestor=ancestor), TemporaryDirectory() as directory:
                project_root = Path(directory) / ancestor / "repository"
                path = project_root / "WeakSimplexConjectureLean/Core/BadImport.lean"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("import Scratch.Experiment\n", encoding="utf-8")
                public_root = project_root / "WeakSimplexConjectureLean.lean"
                findings = audit_file(path, public_root)
                self.assertEqual(len(findings), 1)
                self.assertIn("imports Scratch or Scaffold", findings[0])

    def test_rejects_direct_vendor_import_from_public_root(self) -> None:
        source = "import\n  WeakSimplexConjectureLean.«Vendor».External\n"
        findings = self.audit("WeakSimplexConjectureLean.lean", source)
        self.assertEqual(len(findings), 1)
        self.assertIn("public root imports Vendor directly", findings[0])

    def test_allows_vendor_import_through_project_wrapper(self) -> None:
        source = "import WeakSimplexConjectureLean.Vendor.External\n"
        self.assertEqual(self.audit("WeakSimplexConjectureLean/Gaussian/Shift.lean", source), [])


if __name__ == "__main__":
    main()
