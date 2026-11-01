# Path Grammars: Rocq development

Machine-checked proofs for the paper

> Aarne Talman and Stergios Chatzikyriakidis. *Parsing as Path-Finding: A Stack-Based Grammar for Incremental Syntax.* Submitted to the International Journal of Foundations of Computer Science.

## Contents

| File | Results |
|---|---|
| `PathGrammars.v` | Basic Path Grammars derive exactly the derivation trees of their underlying CNF context-free grammar, and the emitted string is the yield of the tree built (Theorem 2, Corollaries 3 and 4). |
| `ExtendedPathGrammars.v` | Path Grammars with slashed categories and LINK structures generate context-free languages (Theorem 5). |
| `IndexedPathGrammars.v` | Indexed Path Grammars derive exactly the derivation trees of normal-form Linear Indexed Grammars, and conversely (Theorem 8). |

Each file depends only on the standard library (`List`). The development contains no `Admitted` and no axioms beyond those of the core logic. The normal-form construction for LIGs and the cited equivalence of LIG with TAG and CCG are not mechanised.

## Checking the proofs

The files were written for Coq 8.18 (the system has since been renamed Rocq).

    coqc PathGrammars.v ExtendedPathGrammars.v IndexedPathGrammars.v

or, with the included project file,

    coq_makefile -f _CoqProject -o Makefile && make

## How it was made

The mechanisation was developed by the authors in collaboration with an AI assistant (Claude, Anthropic). The authors checked the definitions against the paper, and every theorem is verified by the proof checker.

## License

MIT, see `LICENSE`.
