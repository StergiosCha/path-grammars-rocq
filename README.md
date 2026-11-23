# Rocq development for "Path Grammars: Separating Surface Order from Structure in Incremental Syntax"

Five files, using only the standard library:

- `PathGrammars.v`: basic Path Grammars.
  - Equivalence with CNF context-free grammars and the mutually inverse translations.
  - The recursive form of the shape of derivations.
  - Incrementality, including nested sub-derivations.
  - The flattened stack machine, proved equivalent to the rewrite semantics.
- `ExtendedPathGrammars.v`: single slashes and LINK structures.
  - Weak context-freeness and ε-freeness.
  - The tree-level characterisation and the unique-gap property.
  - Incrementality with pending fillers.
  - The binding example.
- `Doubling.v`: host copying makes structure diverge from the string.
  - The language is a r*, and the term built for a rⁿ has 2ⁿ occurrences of a.
  - Each a rⁿ has exactly one term, and the numbers of a in the expanded yields are exactly the powers of two, which are not ultimately periodic (`unique_output`, `exact_projection`, `not_ultimately_periodic`, contributed by Stergios Chatzikyriakidis).
- `StackedSlashPathGrammars.v`: stacked-slash Path Grammars (filler stacks, per-rule routing (path, def, split-def, split-path), gap sites, category-changing fronting, LINK).
  - `ssg_lig_equivalence`: every grammar generates exactly the strings of a finite linear indexed grammar G♮ (the upper bound).
  - `ssg_tree_characterisation` and `ssg_item_completion`: the terms built are exactly those of the filled derivations.
  - `tder_nonempty` and `ssg_epsilon_free`: fillers are non-empty and the languages are ε-free.
  - `linear_context`: the term built for A/γ is a context with one hole per pending filler, independent of the fillers, and each filler is placed exactly once.
  - `ssg_machine_equivalence` and `ssg_nested_item_completion`: the flattened stack machine and incrementality, including nested sub-derivations.
  - `epg_embedding`, `epg_embedding_trees` and `epg_embedding_language`: the translation of each Extended Path Grammar uses at most one pending filler per category and preserves and reflects its strings and terms.
- `CrossSerial.v`: the verbal-complex grammar VC.
  - `vc_language`: its language is exactly { w w′ | w a non-empty string over a, b }, where w′ replaces a by c and b by d.
  - `vc_unique_term`, `vc_alignment` and `vc_alignment_single`: each string has exactly one term, a left-branching sequence of predicate–argument pairs in which the k-th noun phrase is the argument of the k-th verb.
  - `vc_crossing_fillers` and `pairs_snoc`: the same holds for arbitrary filler terms in the verbal complex, so noun phrases of the same case are never swapped.

Written for Coq 8.18; the system has since been renamed Rocq. To check the proofs:

    coqc PathGrammars.v
    coqc ExtendedPathGrammars.v
    coqc -Q . "" Doubling.v
    coqc -Q . "" StackedSlashPathGrammars.v
    coqc -Q . "" CrossSerial.v

The development contains no `Admitted` and no axioms beyond those of the core logic.

Not mechanised:
- the non-context-freeness of the VC language (pumping lemma);
- the final step of the doubling result: from the failure of ultimate periodicity, via the semilinearity of multiple context-free languages, to {a^(2ⁿ)} not being an MCFL;
- the cited results (parsing complexity of linear indexed grammars, their equivalence with TAG, CCG and Head Grammar, mildly context-sensitive properties);
- the standard link between the rewriting definitions of CFGs and LIGs and the tree-based predicates used here.
