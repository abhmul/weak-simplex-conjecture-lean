#!/usr/bin/env python3
"""Compile the permanent axiom dossier and reject any unexpected dependency."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUIRED_DECLARATIONS = frozenset(
    {
        "WeakSimplex.centered_product_of_posDef",
        "WeakSimplex.centered_product_of_continuous",
        "WeakSimplex.centeredTiltedHalfLine_product_lt_of_ne_one",
        "WeakSimplex.continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine",
        "WeakSimplex.integral_integral_sumDifferenceProduct_eq_sq",
        "WeakSimplex.normalizedCenteredTiltedHalfLine_product",
        "WeakSimplex.exists_adaptiveWitnesses",
        "WeakSimplex.exists_adaptiveWitnesses_of_weakSimplexCov",
        "WeakSimplex.H_pos",
        "WeakSimplex.lowerOrthant_eq_adaptiveProduct",
        "WeakSimplex.lowerOrthant_ge_iid_of_posDef_of_centeredProduct",
        "WeakSimplex.lowerOrthant_ge_iid_of_posDef",
        "WeakSimplex.lowerOrthant_ge_iid",
        "WeakSimplex.lowerOrthant_gt_iid_of_ne_one",
        "WeakSimplex.lowerOrthant_eq_iid_iff",
        "WeakSimplex.multivariateGaussian_one_lowerOrthant",
        "WeakSimplex.symmetricRectangle_eq_iid_iff",
        "WeakSimplex.symmetricRectangle_ge_iid",
        "WeakSimplex.symmetricRectangle_gt_iid_of_ne_one",
        "WeakSimplex.coordinateMax_tail_le_iid",
        "WeakSimplex.coordinateMax_tail_lt_iid_of_ne_one",
        "WeakSimplex.gaussianMax_mgf_lt_regularSimplex",
        "WeakSimplex.gaussianMax_mgf_eq_regularSimplex_iff",
        "WeakSimplex.gramNormalization_eq_one_iff",
        "WeakSimplex.gramGaussianMax_mgf_le_regularSimplex",
        "WeakSimplex.gramGaussianMax_mgf_lt_regularSimplex",
        "WeakSimplex.gramGaussianMax_mgf_eq_regularSimplex_iff",
        "WeakSimplex.decoderSuccessOf_eq_bayesValue",
        "WeakSimplex.bayesValue_lt_regularSimplex",
        "WeakSimplex.bayesValue_eq_regularSimplex_iff",
        "WeakSimplex.weak_simplex",
        "WeakSimplex.weak_simplex_strict",
        "WeakSimplex.weak_simplex_eq_iff_codeGram_eq",
        "WeakSimplex.weak_simplex_of_scoreMaximizingDecoders",
        "WeakSimplex.weak_simplex_strict_of_scoreMaximizingDecoders",
        "WeakSimplex.weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders",
    }
)
PRINT_COMMAND = re.compile(
    r"^[ \t]*#print[ \t]+axioms(?:[ \t]+|\r?\n[ \t]+)([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
PRINTED_RESULT = re.compile(
    r"\A'(.+)'\s+depends on axioms:\s*\[([^]]*)\]\Z", re.DOTALL
)


@dataclass(frozen=True)
class ExpectedCommand:
    declaration: str
    line: int


@dataclass(frozen=True)
class AxiomReport:
    declaration: str
    axioms: tuple[str, ...]
    file_name: str
    line: int
    column: int


def expected_commands(source: str) -> list[ExpectedCommand]:
    """Return declarations and source lines for top-level-looking audit commands."""
    return [
        ExpectedCommand(
            declaration=match.group(1),
            line=source.count("\n", 0, match.start()) + 1,
        )
        for match in PRINT_COMMAND.finditer(source)
    ]


def expected_declarations(source: str) -> list[str]:
    """Return declarations named by the dossier's `#print axioms` commands."""
    return [command.declaration for command in expected_commands(source)]


def printed_axioms(output: str) -> list[AxiomReport]:
    """Parse report-shaped information diagnostics from Lean's JSON output."""
    reports: list[AxiomReport] = []
    for output_line, raw_line in enumerate(output.splitlines(), start=1):
        if not raw_line.strip():
            continue
        try:
            diagnostic = json.loads(raw_line)
        except json.JSONDecodeError as error:
            raise ValueError(
                f"Lean output line {output_line} is not a JSON diagnostic"
            ) from error

        data = diagnostic.get("data")
        if not isinstance(data, str):
            continue
        match = PRINTED_RESULT.fullmatch(data)
        if match is None:
            continue

        position = diagnostic.get("pos")
        if not isinstance(position, dict):
            raise ValueError(f"axiom report on output line {output_line} has no position")
        line = position.get("line")
        column = position.get("column")
        file_name = diagnostic.get("fileName")
        if not isinstance(line, int) or not isinstance(column, int):
            raise ValueError(
                f"axiom report on output line {output_line} has an invalid position"
            )
        if not isinstance(file_name, str):
            raise ValueError(
                f"axiom report on output line {output_line} has no source file"
            )
        if diagnostic.get("severity") != "information":
            raise ValueError(
                f"axiom report on output line {output_line} is not informational"
            )

        axioms = tuple(item.strip() for item in match.group(2).split(",") if item.strip())
        reports.append(
            AxiomReport(
                declaration=match.group(1),
                axioms=axioms,
                file_name=file_name,
                line=line,
                column=column,
            )
        )
    return reports


def validate_audit(
    source: str,
    output: str,
    audit_file: Path,
    required_declarations: frozenset[str] = REQUIRED_DECLARATIONS,
) -> list[str]:
    """Check coverage, source binding, and exact equality with the allowed axiom set."""
    commands = expected_commands(source)
    expected = [command.declaration for command in commands]
    findings: list[str] = []

    if not expected:
        findings.append("the audit source contains no #print axioms commands")

    if len(expected) != len(set(expected)):
        findings.append("the audit source contains duplicate declarations")

    missing_required = sorted(required_declarations - set(expected))
    if missing_required:
        findings.append(
            "required declarations absent from the audit source: "
            + ", ".join(missing_required)
        )

    try:
        parsed = printed_axioms(output)
    except ValueError as error:
        findings.append(str(error))
        return findings

    actual_names = [report.declaration for report in parsed]
    if len(actual_names) != len(set(actual_names)):
        findings.append("Lean output contains duplicate axiom reports")

    missing = sorted(set(expected) - set(actual_names))
    extra = sorted(set(actual_names) - set(expected))
    if missing:
        findings.append("missing axiom reports: " + ", ".join(missing))
    if extra:
        findings.append("unexpected axiom reports: " + ", ".join(extra))
    if len(parsed) != len(expected):
        findings.append(f"expected {len(expected)} axiom reports, found {len(parsed)}")

    expected_lines = {
        command.declaration: command.line
        for command in commands
        if expected.count(command.declaration) == 1
    }
    expected_path = audit_file.resolve()
    for report in parsed:
        if report.declaration not in expected_lines:
            continue
        try:
            report_path = Path(report.file_name).resolve()
        except OSError:
            findings.append(f"{report.declaration}: invalid diagnostic source path")
            continue
        if report_path != expected_path:
            findings.append(
                f"{report.declaration}: diagnostic came from {report.file_name}, not {audit_file}"
            )
        expected_line = expected_lines[report.declaration]
        if report.line != expected_line or report.column != 0:
            findings.append(
                f"{report.declaration}: diagnostic position {report.line}:{report.column} "
                f"does not match #print at {expected_line}:0"
            )

        if len(report.axioms) != len(set(report.axioms)):
            findings.append(f"{report.declaration}: duplicate axiom tokens")
        axioms = frozenset(report.axioms)
        if axioms != ALLOWED_AXIOMS:
            rendered = ", ".join(sorted(axioms))
            findings.append(f"{report.declaration}: unexpected axiom set [{rendered}]")

    return findings


def main() -> int:
    repository = Path(__file__).resolve().parent.parent
    audit_file = repository / "WeakSimplexConjectureLean" / "Audit" / "Axioms.lean"

    try:
        source = audit_file.read_text(encoding="utf-8")
        completed = subprocess.run(
            [
                "lake",
                "env",
                "lean",
                "--json",
                "-DwarningAsError=true",
                str(audit_file),
            ],
            cwd=repository,
            check=False,
            capture_output=True,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired:
        print("axiom audit timed out after 300 seconds", file=sys.stderr)
        return 2
    except (OSError, UnicodeError) as error:
        print(error, file=sys.stderr)
        return 2

    sys.stderr.write(completed.stderr)
    if completed.returncode != 0:
        sys.stdout.write(completed.stdout)
        return completed.returncode

    findings = validate_audit(source, completed.stdout, audit_file)
    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1

    reports = printed_axioms(completed.stdout)
    for report in reports:
        rendered = ", ".join(report.axioms)
        print(f"'{report.declaration}' depends on axioms: [{rendered}]")
    print(f"Axiom audit passed for {len(reports)} declarations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
