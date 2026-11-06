# Rebuild the global manuscript

Work in a non-synchronized directory on BRJD E. The supplied PDF has 46
pages and includes the complete global/mean-width and previous O(rho^6) proof
certificate mapping. TeX Live 2025/pdfLaTeX/latexmk was used.

Run .\build-paper.ps1 from this directory, or invoke latexmk -pdf with
-interaction=nonstopmode -halt-on-error -file-line-error -outdir=build.
The script keeps TeX outputs and all temporary/configuration files under
this directory's build folder. No external figure or bibliography download
is needed. Source sections and source-original must accompany the main TeX.
PDF metadata timestamps can differ on a later build.
