#!/usr/bin/env python3
"""Reject forbidden tokens and imports in project-owned Lean source."""

from __future__ import annotations

import argparse
import bisect
import sys
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path


FORBIDDEN_KEYWORDS = {
    "sorry",
    "admit",
    "axiom",
    "constant",
    "constants",
    "unsafe",
    "native_decide",
}


@dataclass(frozen=True)
class CodeToken:
    value: str
    offset: int
    is_identifier: bool
    is_escaped: bool = False


def _mask_range(chars: list[str], start: int, stop: int) -> None:
    for index in range(start, stop):
        if chars[index] != "\n":
            chars[index] = " "


def _is_letter_like(char: str) -> bool:
    value = ord(char)
    return (
        0x3B1 <= value <= 0x3C9 and value != 0x3BB
        or 0x391 <= value <= 0x3A9 and value not in {0x3A0, 0x3A3}
        or 0x3CA <= value <= 0x3FB
        or 0x1F00 <= value <= 0x1FFE
        or 0x2100 <= value <= 0x214F
        or 0x1D49C <= value <= 0x1D59F
        or 0x00C0 <= value <= 0x00FF and value not in {0x00D7, 0x00F7}
        or 0x0100 <= value <= 0x017F
    )


def _is_subscript_alphanumeric(char: str) -> bool:
    value = ord(char)
    return (
        0x2080 <= value <= 0x2089
        or 0x2090 <= value <= 0x209C
        or 0x1D62 <= value <= 0x1D6A
        or value == 0x2C7C
    )


def _is_identifier_first(char: str) -> bool:
    return (char.isascii() and char.isalpha()) or char == "_" or _is_letter_like(char)


def _is_identifier_rest(char: str) -> bool:
    return (
        (char.isascii() and char.isalnum())
        or char in "_'!?"
        or _is_letter_like(char)
        or _is_subscript_alphanumeric(char)
    )


def _line_comment_end(source: str, start: int) -> int:
    stop = source.find("\n", start + 2)
    return len(source) if stop == -1 else stop


def _block_comment_end(source: str, start: int) -> int:
    depth = 1
    index = start + 2
    while index < len(source) and depth:
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif source.startswith("-/", index):
            depth -= 1
            index += 2
        else:
            index += 1
    return index


def _quoted_escape_end(source: str, start: int) -> int:
    if start + 1 >= len(source):
        return len(source)
    escaped = source[start + 1]
    if escaped == "x":
        return min(start + 4, len(source))
    if escaped == "u":
        return min(start + 6, len(source))
    if escaped == "\n":
        index = start + 2
        while index < len(source) and source[index].isspace():
            index += 1
        return index
    return start + 2


def _raw_string_end(source: str, start: int) -> int | None:
    if source[start] != "r":
        return None
    quote = start + 1
    while quote < len(source) and source[quote] == "#":
        quote += 1
    if quote >= len(source) or source[quote] != '"':
        return None
    closing = '"' + "#" * (quote - start - 1)
    stop = source.find(closing, quote + 1)
    return len(source) if stop == -1 else stop + len(closing)


def _escaped_identifier_end(source: str, start: int) -> int:
    stop = source.find("»", start + 1)
    return len(source) if stop == -1 else stop + 1


def _identifier_end(source: str, start: int) -> int:
    stop = start + 1
    while stop < len(source) and _is_identifier_rest(source[stop]):
        stop += 1
    return stop


def _is_ascii_digit(char: str) -> bool:
    return "0" <= char <= "9"


def _take_number_digits_end(
    source: str, start: int, is_digit: Callable[[str], bool]
) -> int:
    index = start
    while index < len(source):
        if source[index] == "_" or is_digit(source[index]):
            index += 1
        else:
            break
    return index


def _number_literal_end(source: str, start: int) -> int | None:
    """Return the successful Lean numeral/scientific token boundary at `start`."""

    if not _is_ascii_digit(source[start]):
        return None

    if source[start] == "0" and start + 1 < len(source):
        prefix = source[start + 1]
        if prefix in "bB":
            return _take_number_digits_end(
                source, start + 2, lambda char: char in "01"
            )
        if prefix in "oO":
            return _take_number_digits_end(
                source, start + 2, lambda char: "0" <= char <= "7"
            )
        if prefix in "xX":
            return _take_number_digits_end(
                source,
                start + 2,
                lambda char: _is_ascii_digit(char)
                or "a" <= char <= "f"
                or "A" <= char <= "F",
            )

    index = _take_number_digits_end(source, start + 1, _is_ascii_digit)
    if source.startswith("..", index):
        return index

    if index < len(source) and source[index] == ".":
        index += 1
        if index < len(source) and _is_ascii_digit(source[index]):
            index = _take_number_digits_end(source, index, _is_ascii_digit)

    if index < len(source) and source[index] in "eE":
        exponent = index + 1
        if exponent < len(source) and source[exponent] in "+-":
            exponent += 1
        if exponent < len(source) and _is_ascii_digit(source[exponent]):
            return _take_number_digits_end(source, exponent, _is_ascii_digit)
        return index

    # Lean rejects an identifier immediately after a bare decimal point. Returning after the dot
    # still preserves every following character for conservative token scanning on malformed input.
    return index


def _char_literal_end(source: str, start: int) -> int | None:
    value_end = start + 1
    if value_end >= len(source) or source[value_end] == "\n":
        return None
    if source[value_end] == "\\":
        value_end = _quoted_escape_end(source, value_end)
    else:
        value_end += 1
    if value_end < len(source) and source[value_end] == "'":
        return value_end + 1
    return None


def _ordinary_string_end(source: str, start: int) -> int:
    index = start + 1
    while index < len(source):
        if source[index] == "\\":
            index = _quoted_escape_end(source, index)
        elif source[index] == '"':
            return index + 1
        else:
            index += 1
    return len(source)


def _mask_potential_interpolated_string(
    chars: list[str], source: str, start: int
) -> int:
    # Arbitrary Lean macros can consume `interpolatedStr`, including a bare quoted string without
    # an `s!`/`m!`/`f!` prefix. Normal-string text remains visible even while this view navigates
    # its possible interpolation holes; arbitrary term syntax makes lexical hole boundaries an
    # unsafe basis for hiding any of that text.
    index = start + 1
    while index < len(source):
        if source[index] == "\\":
            index = _quoted_escape_end(source, index)
        elif source[index] == '"':
            return index + 1
        elif source[index] == "{":
            index = _scan_interpolation_hole(chars, source, index + 1)
        else:
            index += 1
    return len(source)


def _scan_interpolation_hole(chars: list[str], source: str, start: int) -> int:
    depth = 1
    index = start
    while index < len(source):
        if source[index] == "«":
            index = _escaped_identifier_end(source, index)
            continue
        if source.startswith("--", index):
            stop = _line_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        if source.startswith("/-", index):
            stop = _block_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        number_end = _number_literal_end(source, index)
        if number_end is not None:
            index = number_end
            continue
        raw_end = _raw_string_end(source, index)
        if raw_end is not None:
            index = raw_end
            continue
        if source[index] == '"':
            index = _mask_potential_interpolated_string(chars, source, index)
            continue
        if source[index] == "'":
            char_end = _char_literal_end(source, index)
            if char_end is not None:
                index = char_end
                continue
        if _is_identifier_first(source[index]):
            index = _identifier_end(source, index)
            continue
        if source[index] == "{":
            depth += 1
        elif source[index] == "}":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return len(source)


def _mask_ordinary_syntax_view(source: str) -> str:
    chars = list(source)
    index = 0
    while index < len(source):
        if source[index] == "«":
            index = _escaped_identifier_end(source, index)
            continue
        if source.startswith("--", index):
            stop = _line_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        if source.startswith("/-", index):
            stop = _block_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        number_end = _number_literal_end(source, index)
        if number_end is not None:
            index = number_end
            continue
        raw_end = _raw_string_end(source, index)
        if raw_end is not None:
            index = raw_end
            continue
        if source[index] == '"':
            index = _ordinary_string_end(source, index)
            continue
        if source[index] == "'":
            char_end = _char_literal_end(source, index)
            if char_end is not None:
                index = char_end
                continue
        if _is_identifier_first(source[index]):
            index = _identifier_end(source, index)
            continue
        index += 1

    return "".join(chars)


def _mask_potential_interpolation_view(source: str) -> str:
    chars = list(source)
    index = 0
    while index < len(source):
        if source[index] == "«":
            index = _escaped_identifier_end(source, index)
            continue
        if source.startswith("--", index):
            stop = _line_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        if source.startswith("/-", index):
            stop = _block_comment_end(source, index)
            _mask_range(chars, index, stop)
            index = stop
            continue
        number_end = _number_literal_end(source, index)
        if number_end is not None:
            index = number_end
            continue
        raw_end = _raw_string_end(source, index)
        if raw_end is not None:
            index = raw_end
            continue
        if source[index] == '"':
            index = _mask_potential_interpolated_string(chars, source, index)
            continue
        if source[index] == "'":
            char_end = _char_literal_end(source, index)
            if char_end is not None:
                index = char_end
                continue
        if _is_identifier_first(source[index]):
            index = _identifier_end(source, index)
            continue
        index += 1

    return "".join(chars)


def mask_comments_and_literals(source: str) -> str:
    """Mask comments recognized by both structural views and preserve all other text."""

    # A quoted token may be an ordinary Lean string or an `interpolatedStr` consumed by an
    # arbitrary macro. The two structural views navigate those alternatives independently, but
    # both retain all normal-string text: custom syntax can consume quotes or braces in ways a
    # bounded lexer cannot reconstruct. Raw strings and character literals are also retained:
    # macros can reparse their values as terms. Only comments masked by both views are hidden.
    # Thus desynchronization in either view cannot hide code retained by the other; the deliberate
    # cost is rejecting forbidden spellings in every literal and escaped identifier.
    ordinary = _mask_ordinary_syntax_view(source)
    potential = _mask_potential_interpolation_view(source)
    return "".join(
        " "
        if source[index] != "\n" and ordinary[index] == " " and potential[index] == " "
        else source[index]
        for index in range(len(source))
    )


def code_tokens(code: str) -> list[CodeToken]:
    tokens: list[CodeToken] = []
    index = 0
    while index < len(code):
        if code[index].isspace():
            index += 1
            continue

        if code[index] == "«":
            stop = code.find("»", index + 1)
            if stop != -1:
                tokens.append(CodeToken(code[index + 1 : stop], index, True, True))
                index = stop + 1
                continue

        number_end = _number_literal_end(code, index)
        if number_end is not None:
            tokens.append(CodeToken(code[index:number_end], index, False))
            index = number_end
            continue

        if code[index] == "'":
            char_end = _char_literal_end(code, index)
            if char_end is not None:
                index = char_end
                continue

        if _is_identifier_first(code[index]):
            stop = _identifier_end(code, index)
            tokens.append(CodeToken(code[index:stop], index, True))
            index = stop
            continue

        tokens.append(CodeToken(code[index], index, False))
        index += 1

    return tokens


def imported_modules(tokens: list[CodeToken]) -> list[tuple[list[str], int]]:
    modules: list[tuple[list[str], int]] = []
    for index, token in enumerate(tokens):
        if token.value != "import" or token.is_escaped:
            continue

        cursor = index + 1
        if (
            cursor < len(tokens)
            and tokens[cursor].value == "all"
            and not tokens[cursor].is_escaped
        ):
            cursor += 1
        if cursor >= len(tokens) or not tokens[cursor].is_identifier:
            continue

        segments = [tokens[cursor].value]
        cursor += 1
        while cursor + 1 < len(tokens) and tokens[cursor].value == ".":
            if not tokens[cursor + 1].is_identifier:
                break
            segments.append(tokens[cursor + 1].value)
            cursor += 2
        modules.append((segments, token.offset))
    return modules


def _location(source: str, offset: int) -> tuple[int, int]:
    newline_offsets = [-1]
    newline_offsets.extend(index for index, char in enumerate(source) if char == "\n")
    line_index = bisect.bisect_left(newline_offsets, offset) - 1
    line = line_index + 1
    column = offset - newline_offsets[line_index]
    return line, column


def _is_nonproduction_path(path: Path, public_root: Path) -> bool:
    try:
        relative_path = path.resolve().relative_to(public_root.resolve().parent)
    except ValueError:
        return False
    return any(part in {"Scratch", "Scaffold"} for part in relative_path.parts)


def audit_file(path: Path, public_root: Path) -> list[str]:
    source = path.read_text(encoding="utf-8")
    code = mask_comments_and_literals(source)
    tokens = code_tokens(code)
    findings: list[str] = []

    for token in tokens:
        is_forbidden_keyword = token.value in FORBIDDEN_KEYWORDS
        is_sorry_axiom = token.value == "sorryAx"
        if token.is_identifier and (is_forbidden_keyword or is_sorry_axiom):
            line, column = _location(source, token.offset)
            findings.append(f"{path}:{line}:{column}: forbidden Lean token '{token.value}'")

    imports = imported_modules(tokens)
    if not _is_nonproduction_path(path, public_root):
        for segments, offset in imports:
            is_root_nonproduction_module = segments[0] in {"Scratch", "Scaffold"}
            is_project_module = len(segments) >= 2 and segments[0] == "WeakSimplexConjectureLean"
            is_project_nonproduction_module = (
                is_project_module and segments[1] in {"Scratch", "Scaffold"}
            )
            if is_root_nonproduction_module or is_project_nonproduction_module:
                line, column = _location(source, offset)
                findings.append(
                    f"{path}:{line}:{column}: production module imports Scratch or Scaffold"
                )

    if path.resolve() == public_root.resolve():
        for segments, offset in imports:
            if len(segments) >= 2 and segments[:2] == ["WeakSimplexConjectureLean", "Vendor"]:
                line, column = _location(source, offset)
                findings.append(f"{path}:{line}:{column}: public root imports Vendor directly")

    return findings


def lean_files(paths: Iterable[Path]) -> list[Path]:
    files: set[Path] = set()
    for path in paths:
        if path.is_dir():
            files.update(candidate for candidate in path.rglob("*.lean") if candidate.is_file())
        elif path.suffix == ".lean" and path.is_file():
            files.add(path)
        else:
            raise FileNotFoundError(f"not a Lean file or directory: {path}")
    return sorted(files)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--public-root", type=Path, required=True)
    parser.add_argument("paths", nargs="+", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    findings: list[str] = []
    try:
        if not args.public_root.is_file():
            raise FileNotFoundError(f"public root does not exist: {args.public_root}")
        files = lean_files(args.paths)
        if args.public_root.resolve() not in {path.resolve() for path in files}:
            raise FileNotFoundError("public root is not included in the audited paths")
        for path in files:
            findings.extend(audit_file(path, args.public_root))
    except (OSError, UnicodeError) as error:
        print(error, file=sys.stderr)
        return 2

    if findings:
        print("\n".join(findings), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
