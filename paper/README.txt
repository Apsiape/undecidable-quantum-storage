Undecidable quantum storage with seven elementary gates
Seth Douglas and Nidhal Mghirbi
Version 2.1.0, November 2026

Build: python -I -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY].
Requires Python 3 and pdflatex with the packages loaded by main.tex.
The build runs pdflatex three times without shell escape and rejects warnings,
unresolved references and overfull or underfull boxes.

main.pdf is the compiled preprint (83 pages); abstract.txt is the plain-text
abstract. Section 9 retains Theorem B and Proposition 9.8. Section 10 adds
Theorem D, stretched-exponential undecidable-window storage in four dimensions
under whole-site noise. Appendices A--C retain their earlier results;
Appendices D--F give the new periodic-calendar, exclusive-dispatch and
central-strip source proofs. Appendix G prints conditional Theorem G.1 and
describes Lean verification of it and Lemma 6.6; the physical constructions
remain outside that verification. The release repository also contains the
lean/ source package, scope and reproduction instructions. The bibliography
is references.tex.
