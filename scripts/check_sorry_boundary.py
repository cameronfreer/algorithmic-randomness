#!/usr/bin/env python3
"""Enforce the sorry boundary.

Policy:

1. Everything transitively imported by `AlgorithmicRandomness.lean` — the production root spine — is
   sorry-free.
2. Work in progress lives under `AlgorithmicRandomnessExperimental/` and is never imported by the
   root spine. It may contain sorries; it still has to typecheck, which the separate
   `AlgorithmicRandomnessExperimental` lake target ensures.
3. Promotion into the root spine requires removing all sorries. Promotion is the
   reviewable event: a file appearing in the transitive closure of
   `AlgorithmicRandomness.lean` is a claim that it is finished.

This script enforces 1 and 2. Comments and string literals are stripped before scanning, with
nested block comments handled, so neither an `import` nor a `sorry` can hide inside a comment and
neither can be invented by one inside a string. It computes the import closure from the source text
rather
than from build artefacts, so it works on a clean checkout and cannot be fooled by a
stale `.lake`.

Usage: scripts/check_sorry_boundary.py   (from anywhere inside the repo)
Exit status 1 on any violation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT_MODULE = "AlgorithmicRandomness"
EXPERIMENTAL_PREFIX = "AlgorithmicRandomnessExperimental"

# `sorry` and friends as whole words. `sorryAx` is the kernel-level form; `admit` is the
# tactic alias. Substring matches like `sorryFree` are excluded by the word boundaries.
SORRY_RE = re.compile(r"\b(sorry|sorryAx|admit)\b")
# Several imports may appear on one line, so this is scanned with `finditer`, not matched once.
IMPORT_RE = re.compile(r"(?:^|\s)import\s+([A-Za-z0-9_.]+)")


def strip_comments(text: str) -> list[str]:
    """Blank out Lean comments, preserving line count and column positions.

    Handles nested block comments (`/- /- -/ -/`, and so docstrings `/-- ... -/` too), line
    comments, and string literals, so that neither an `import` nor a `sorry` can hide inside a
    comment and neither can be invented by one appearing inside a string.
    """
    lines: list[str] = []
    cur: list[str] = []
    depth = 0
    in_string = False
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "\n":
            lines.append("".join(cur))
            cur = []
            i += 1
            continue
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                cur.append("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                cur.append("  ")
                i += 2
                continue
            cur.append(" ")
            i += 1
            continue
        if in_string:
            if ch == "\\":
                cur.append("  ")
                i += 2
                continue
            if ch == '"':
                in_string = False
            cur.append(" ")
            i += 1
            continue
        if ch == '"':
            in_string = True
            cur.append(" ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            j = text.find("\n", i)
            j = n if j == -1 else j
            cur.append(" " * (j - i))
            i = j
            continue
        if ch == "/" and nxt == "-":
            depth += 1
            cur.append("  ")
            i += 2
            continue
        cur.append(ch)
        i += 1
    lines.append("".join(cur))
    return lines


def repo_root() -> Path:
    here = Path(__file__).resolve().parent.parent
    if not (here / "lakefile.toml").exists():
        sys.exit(f"check_sorry_boundary: no lakefile.toml at {here}")
    return here


def module_path(root: Path, module: str) -> Path | None:
    """Source file for a repo-local module name, or None if it is not ours.

    Locality is decided by whether the file exists in the repo, not by a namespace
    prefix, so both `AlgorithmicRandomness.*` and `AlgorithmicRandomnessExperimental.*` resolve. (Those are
    separate top-level namespaces on purpose: Lake's `isLocalModule` treats a name
    prefix as library ownership, so `AlgorithmicRandomness.Experimental.*` would be claimed by the
    strict `AlgorithmicRandomness` library too and its `sorry`s would become build errors.)
    """
    p = root / (module.replace(".", "/") + ".lean")
    return p if p.exists() else None


def imports_of(path: Path) -> list[str]:
    out = []
    for line in strip_comments(path.read_text()):
        out.extend(m.group(1) for m in IMPORT_RE.finditer(line))
    return out


def closure(root: Path) -> set[str]:
    """Transitive repo-local import closure of the root module."""
    seen: set[str] = set()
    stack = [ROOT_MODULE]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        p = module_path(root, mod)
        if p is None:
            continue  # mathlib or a missing module; `lake build` is the judge of those
        seen.add(mod)
        stack.extend(imports_of(p))
    return seen


def sorries_in(path: Path) -> list[tuple[int, str]]:
    hits = []
    for i, line in enumerate(strip_comments(path.read_text()), 1):
        if SORRY_RE.search(line):
            hits.append((i, line.strip()))
    return hits


def main() -> int:
    root = repo_root()
    spine = closure(root)
    status = 0

    # (1) the spine is sorry-free
    for mod in sorted(spine):
        p = module_path(root, mod)
        assert p is not None
        for lineno, text in sorries_in(p):
            rel = p.relative_to(root)
            print(f"{rel}:{lineno}: sorry in the root import spine — {text}",
                  file=sys.stderr)
            status = 1

    # (2) no Experimental module is in the spine
    for mod in sorted(spine):
        if mod == EXPERIMENTAL_PREFIX or mod.startswith(EXPERIMENTAL_PREFIX + "."):
            print(f"{mod} is reachable from {ROOT_MODULE}.lean: experimental modules must "
                  f"not be imported by the production root spine", file=sys.stderr)
            status = 1

    # Informational: what is staged outside the spine.
    exp_dir = root / "AlgorithmicRandomnessExperimental"
    staged = sorted(p.relative_to(root) for p in exp_dir.rglob("*.lean")) if exp_dir.is_dir() else []
    n_sorry = sum(1 for p in staged if sorries_in(root / p))

    if status == 0:
        print(f"check_sorry_boundary: {len(spine)} spine module(s) sorry-free; "
              f"{len(staged)} experimental module(s) outside the spine "
              f"({n_sorry} containing sorries)")
    return status


if __name__ == "__main__":
    sys.exit(main())
