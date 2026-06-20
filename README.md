[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/hybrid_logic_lean_revisited/build.yml?label=Lean%204)](https://github.com/catskillsresearch/hybrid_logic_lean_revisited/actions/workflows/build.yml)

# hybrid_logic_lean_revisited

Completing the **completeness theorem** for Alex Oltean's Lean 4 formalization of the
hybrid logic *L(∀)*.

This repository starts from Alex Oltean's
[`hybrid_logic_lean`](https://github.com/alexoltean61/hybrid_logic_lean) (archived),
ports it to **Lean v4.30.0 / mathlib v4.30.0**, and closes the completeness gap that
his BA thesis (`oltean_thesis.pdf`) left open. The mathematics follows Patrick
Blackburn's *"Hybrid Completeness"* (1998), included as `blackburn1998.pdf`.

The article-length narrative, background, motivation, related work, and the discussion
of the completeness proof and its freshness mechanism live in **[`arxiv.md`](arxiv.md)**.

## Building

Requires **Lean v4.30.0** and **mathlib v4.30.0** (pinned in `lean-toolchain` and
`lake-manifest.json`).

```bash
lake build
```

## Status

- Build environment ported to Lean v4.30.0 / mathlib v4.30.0.
- Base modules ported and compiling.
- Completeness proof: in progress (see `arxiv.md` for the approach).

## Attribution

Builds on **Alex Oltean**'s original formalization; mathematics from **Blackburn 1998**;
the disjoint-sum (`N ⊕ ℕ`) Henkin construction was suggested by **Bud Mishra**. See
`arxiv.md` (Acknowledgments) and `NOTICE` for details.

## Contributions and Collaboration

This repository functions strictly as a unilateral broadcast of public code for
educational and research purposes.

* **Pull Requests and Issues:** This project does not accept external Pull Requests,
  code contributions, or modifications, and tracking features have been disabled.
* **Forks:** Users are free to fork or clone this repository and modify the code on
  their own profiles in accordance with the Apache 2.0 License.

## License

The original code under `Hybrid/` is the work of **Alex Oltean** and was published
upstream ([`hybrid_logic_lean`](https://github.com/alexoltean61/hybrid_logic_lean))
**without an explicit license**; all rights to it remain with its author. It is included
and modified here in good faith for non-commercial academic research, with attribution,
and no rights over the original work are claimed.

The modifications and the new files at the repository root are offered under the
**Apache License, Version 2.0** (see `LICENSE` and `NOTICE`), to the extent they are
separable from the original work. The software is provided "AS IS" without warranties of
any kind.
