Undecidable quantum storage with seven elementary gates
Seth Douglas and Nidhal Mghirbi
Version 1.0.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3 and pdflatex with the packages loaded by main.tex. The bibliography is in references.tex. The build
runs pdflatex three times without shell escape and rejects warnings, unresolved references and overfull or underfull
boxes. main.pdf is the compiled preprint (46 pages); abstract.txt is the abstract as plain text. main.tex includes the
sections in sections/ (the appendices are folded.tex, fold-controls.tex and coexistence.tex) and the bibliography in
references.tex.
No publication or submission is performed by the build.
