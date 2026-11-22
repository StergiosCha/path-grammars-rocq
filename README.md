# Rocq development for "Parsing as Path-Finding: A Stack-Based Grammar for Incremental Syntax"

Six files, using only the standard library:

- `PathGrammars.v`: basic Path Grammars.
  - Equivalence with CNF context-free grammars (Theorem 2, Corollary 3) and the mutually inverse translations.
  - The recursive form of Proposition 1.
  - Incrementality, including nested sub-derivations (Corollary 4).
  - The flattened stack machine of Remark 1, proved equivalent to the rewrite semantics.
- `ExtendedPathGrammars.v`: slashed categories and LINK structures.
  - Weak context-freeness (Theorem 5) and ε-freeness (Corollary 6).
  - The tree-level characterisation (Theorem 7) and the unique-gap property.
  - Incrementality with pending fillers (Corollary 8).
  - The binding example (4).
- `IndexedPathGrammars.v`: Indexed Path Grammars.
  - Equivalence with normal-form Linear Indexed Grammars (Theorem 11).
  - Incrementality (Corollary 12).
- `LIGNormalForm.v`: the LIG normal form (Lemma 10). Every LIG language is an IPG language.
- `Doubling.v`: host copying makes structure diverge from the string (Corollary 9). The language is a r*, and the term built for a rⁿ has 2ⁿ occurrences of a.
- `CrossSerial.v`: the grammar of Example 5 generates exactly { aⁿbᵐcⁿdᵐ | n, m ≥ 1 } (Proposition 14, language part).

Written for Coq 8.18; the system has since been renamed Rocq. To check the proofs:

    coqc PathGrammars.v
    coqc ExtendedPathGrammars.v
    coqc IndexedPathGrammars.v
    coqc -Q . "" CrossSerial.v
    coqc -Q . "" LIGNormalForm.v
    coqc -Q . "" Doubling.v

The development contains no `Admitted` and no axioms beyond those of the core logic.

Not mechanised:
- the non-context-freeness of aⁿbᵐcⁿdᵐ (pumping lemma) and the dependency alignment in Proposition 14;
- the final step of Corollary 9: {a^(2ⁿ)} is not semilinear, hence not a multiple context-free language;
- the cited results (parsing complexity, the equivalence of LIG with TAG, CCG and Head Grammar, mildly context-sensitive properties);
- the standard link between the rewriting definitions of CFGs and LIGs and the tree-based predicates used here.
