# Simplex Stability in Lean

**Explicit Stability of the Weak Simplex Bound** — manuscript and verified
Lean formalization of global quantitative bounds, spherical mean-width
stability, ordered channel transitions, and the strict-normal small-shell
expansion with an $O(\rho^6)$ remainder.

[Read the paper (PDF)](paper_main.pdf) ·
[Download release v1.0.0](https://github.com/ab8266339/simplex-stability-lean/releases/tag/v1.0.0) ·
[Proof map](lean/PROOF_MAP_GLOBAL.md) ·
[Verification certificate](lean/evidence/verification.json)

## Results

- Explicit global Gaussian orthant comparison, including singular admissible
  covariances, with the manuscript's exact constants.
- Centroid estimates and Gram/Procrustes recovery bounds; decoding, rank and
  unused-energy consequences.
- Mean-width stability for the actual finite convex hull and normalized sphere
  measure, with the Gaussian representation and the conventional
  $h_K(u)+h_K(-u)$ integral identified.
- Ordered channel-parameter crossings and the exact strict-normal optimizer on
  sufficiently small Procrustes shells, with a quantified $O(\rho^6)$ remainder.

The global results apply for $m\ge2$ under their stated assumptions.
The local results retain $m\ge3$, the strict curvature gap and a sufficiently
small radius. The local radius and remainder constant are proved to exist;
effective numerical values are not certified. Numerical diagnostics and
learning experiments in the manuscript are outside the formal certificate.

## Verification

| Item | Verified release |
| --- | --- |
| Lean | 4.31.0 |
| Mathlib commit | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Source modules in the verified closure | 216, including 52 vendored foundation modules |
| Selected public declarations audited | 91 |
| Kernel trust level | 0 |
| Axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| Recorded run | `20261106-180522-470580` |
| Verifier regression tests | 44 passed |
| Manuscript | 46 pages |

The verifier builds the entire project source closure in an empty output
directory and checks source hashes, dependency pins, import closure and axiom
reports. Project build binaries are not part of the release. The original
94 local modules are unchanged from the preceding reviewed artifact.
The module and audit counts describe this release, not every sentence of
the manuscript. Eight Grok Build sessions and independent agent reviews are
included as supporting evidence; the Lean kernel provides the proof check.

## Reproduce

Install Git, Python 3 and elan/Lean. From the repository root:

~~~sh
cd lean
lake update
lake exe cache get
lake env python reproduce.py
~~~

The toolchain and Mathlib revision are pinned. See
[the Lean README](lean/README.md) for the verifier's behavior and
[the paper build instructions](paper_source/BUILD.md) for rebuilding the TeX.
The supplied verification was run on Windows; other platforms require their
corresponding Lean toolchain and Python environment.

## Contents

- `paper_main.pdf`: the current manuscript.
- `paper_source/`: TeX, build instructions and preserved original sources.
- `lean/`: source modules, verifier, pinned Lake configuration, proof map,
  source manifests, licenses and compiler/cross-review evidence.
- `evidence/paper/`: paper source checks, PDF QA, contact sheets and build logs.
- `evidence/release/`: original bundle metadata and post-packaging checks.
- `PUBLICATION_MANIFEST.json`: hashes of the files in this GitHub publication.

The release provides the PDF, the standalone Lean ZIP, the complete paper/Lean
bundle and a SHA-256 checksum file. The original ZIP files are uploaded without
changes, so their previously recorded hashes remain valid.

## Provenance and licenses

The 52 vendored modules retain their upstream license notices and source
provenance. See [VENDOR_PROVENANCE.json](lean/VENDOR_PROVENANCE.json),
[licenses/](lean/licenses/) and the vendor's own notices.
Those licenses apply to their corresponding upstream material; this
publication does not assign a new blanket license to the original manuscript
or project additions.

## 中文说明

本仓库整理弱单纯形界的显式稳定性结果：全局界、质心与几何恢复估计、
平均宽度，以及局部严格法向最优解和 $O(\rho^6)$ 展开。216 个源码模块、
91 个公开定理入口已完成 Lean 内核验证；论文为 46 页。定理假设、复现步骤、
源码哈希和交叉审查材料均随仓库提供，完整成果包见 Release。
