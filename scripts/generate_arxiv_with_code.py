#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

FILES = [
    "Hybrid.lean",
    "Hybrid/Util.lean",
    "Hybrid/Form.lean",
    "Hybrid/Tautology.lean",
    "Hybrid/Substitutions.lean",
    "Hybrid/Proof.lean",
    "Hybrid/Truth.lean",
    "Hybrid/ListUtils.lean",
    "Hybrid/ProofUtils.lean",
    "Hybrid/Soundness.lean",
    "Hybrid/RenameBound.lean",
    "Hybrid/FormCountable.lean",
    "Hybrid/Lindenbaum.lean",
    "Hybrid/LanguageExtension.lean",
    "Hybrid/ExistenceLemma.lean",
    "Hybrid/CompletedModel.lean",
    "Hybrid/Completeness.lean",
]


def main() -> None:
    arxiv = (ROOT / "arxiv.md").read_text()
    # Drop title + optional review pointer block through first --- after title
    body = arxiv
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
    )
    parts.append(
        "# Finishing Oltean's Completeness Proof in Lean 4 for Hybrid Logic *L(∀)* "
        "— full narrative + complete Lean source\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and all library "
        "`.lean` files in dependency order (`Hybrid.lean`).*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the review pointer at the top). "
        "This file appends **Appendix A: Complete Lean source** with every line "
        "of the formalization inlined below.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **§1–§9** | Full `arxiv.md` narrative (abstract through scorecard) |\n")
    parts.append("| **Appendix A** | Complete Lean 4 source, one subsection per file |\n\n")
    parts.append("### Appendix A — file index\n\n")

    total_lines = 0
    for f in FILES:
        n = len((ROOT / f).read_text().splitlines())
        total_lines += n
        parts.append(f"- [`{f}`](#{f.replace('/', '').replace('.', '').lower()}) — {n} lines\n")

    parts.append(f"\n**Total:** {len(FILES)} files, {total_lines} lines of Lean.\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body.rstrip())
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append(
        "Files appear in `Hybrid.lean` import order. "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )

    for f in FILES:
        content = (ROOT / f).read_text().rstrip() + "\n"
        n = len(content.splitlines())
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"Wrote {out} ({len(out.read_text().splitlines())} lines)")


if __name__ == "__main__":
    main()
