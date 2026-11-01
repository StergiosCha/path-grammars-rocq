(* ===================================================================== *)
(*  Path Grammars: mechanised weak and strong equivalence with CFGs      *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc PathGrammars.v).                         *)
(* ===================================================================== *)

Require Import List.
Import ListNotations.

Section PathGrammars.

Variables terminal nonterminal : Type.

(* ---------------------------------------------------------------- *)
(* Path grammar rules.                                               *)
(*   PRule A B C  encodes  A -> [B] C   (C is expanded now, i.e. it  *)
(*                                       is the left daughter; B is  *)
(*                                       deferred on the stack and   *)
(*                                       is the right daughter)      *)
(*   TRule A a    encodes  A -> a                                    *)
(* ---------------------------------------------------------------- *)
Inductive prule : Type :=
  | PRule : nonterminal -> nonterminal -> nonterminal -> prule
  | TRule : nonterminal -> terminal -> prule.

(* Unlabelled bracketings ("terms"); Node l r has left part l. *)
Inductive term : Type :=
  | Leaf : terminal -> term
  | Node : term -> term -> term.

Fixpoint yield (t : term) : list terminal :=
  match t with
  | Leaf a => [a]
  | Node l r => yield l ++ yield r
  end.

(* The focus of an item X : phi is a single non-terminal or a
   completed term. *)
Inductive focus : Type :=
  | FNT : nonterminal -> focus
  | FT  : term -> focus.

Definition item : Type := (list nonterminal * focus)%type.

Variable R : list prule.

(* Multi-step derivation  c  =>*_s  c'  with emitted string s.
   RW3 embeds a sub-derivation from the empty stack, exactly as in
   the paper.                                                       *)
Inductive derives : item -> list terminal -> item -> Prop :=
  | d_refl : forall c, derives c [] c
  | d_rw1 : forall X A B C s c',
      In (PRule A B C) R ->
      derives (B :: X, FNT C) s c' ->
      derives (X, FNT A) s c'
  | d_rw2 : forall X A a s c',
      In (TRule A a) R ->
      derives (X, FT (Leaf a)) s c' ->
      derives (X, FNT A) (a :: s) c'
  | d_rw3 : forall X B t tB s1 s2 c',
      derives ([], FNT B) s1 ([], FT tB) ->
      derives (X, FT (Node t tB)) s2 c' ->
      derives (B :: X, FT t) (s1 ++ s2) c'.

Definition pg_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, derives ([], FNT S) w ([], FT t).

(* The CFG G_P read off from P:  A -> [B]C  becomes  A -> C B.
   cfg_der A w t : A derives w with derivation tree (bracketing) t. *)
Inductive cfg_der : nonterminal -> list terminal -> term -> Prop :=
  | c_term : forall A a,
      In (TRule A a) R -> cfg_der A [a] (Leaf a)
  | c_bin : forall A B C w1 w2 t1 t2,
      In (PRule A B C) R ->
      cfg_der C w1 t1 ->
      cfg_der B w2 t2 ->
      cfg_der A (w1 ++ w2) (Node t1 t2).

Definition cfg_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, cfg_der S w t.

Lemma cfg_der_yield : forall A w t, cfg_der A w t -> yield t = w.
Proof.
  intros A w t H; induction H; simpl; congruence.
Qed.

Lemma derives_trans : forall c1 s1 c2 s2 c3,
  derives c1 s1 c2 -> derives c2 s2 c3 -> derives c1 (s1 ++ s2) c3.
Proof.
  intros c1 s1 c2 s2 c3 H1 H2.
  induction H1.
  - exact H2.
  - eapply d_rw1; eauto.
  - simpl. eapply d_rw2; eauto.
  - rewrite <- app_assoc. eapply d_rw3; eauto.
Qed.

(* ---------------- Completeness:  G_P  ==>  P -------------------- *)

Lemma cfg_to_path : forall A w t,
  cfg_der A w t -> forall X, derives (X, FNT A) w (X, FT t).
Proof.
  intros A w t H; induction H; intros X.
  - rewrite <- (app_nil_r [a]). simpl.
    eapply d_rw2; [exact H | apply d_refl].
  - eapply d_rw1; [exact H |].
    apply derives_trans with (c2 := (B :: X, FT t1)).
    + apply IHcfg_der1.
    + rewrite <- (app_nil_r w2).
      eapply d_rw3; [apply IHcfg_der2 | apply d_refl].
Qed.

(* ---------------- Soundness:  P  ==>  G_P ------------------------ *)

(* A list of non-terminals derives a concatenation, with one tree each. *)
Inductive cfg_ders : list nonterminal -> list terminal -> list term -> Prop :=
  | cs_nil : cfg_ders [] [] []
  | cs_cons : forall B X w1 w2 t ts,
      cfg_der B w1 t -> cfg_ders X w2 ts ->
      cfg_ders (B :: X) (w1 ++ w2) (t :: ts).

(* Attaching the subtrees of the deferred right sisters, innermost first. *)
Fixpoint attach (t : term) (ts : list term) : term :=
  match ts with
  | [] => t
  | u :: us => attach (Node t u) us
  end.

(* content c w T : completing item c, the not-yet-emitted remainder of
   the input is w and the final bracketing is T.                     *)
Definition content (c : item) (w : list terminal) (T : term) : Prop :=
  match c with
  | (X, FNT A) => exists w1 w2 tA ts,
      w = w1 ++ w2 /\ cfg_der A w1 tA /\ cfg_ders X w2 ts /\ T = attach tA ts
  | (X, FT t) => exists ts, cfg_ders X w ts /\ T = attach t ts
  end.

Lemma derives_content : forall c s c',
  derives c s c' -> forall w T, content c' w T -> content c (s ++ w) T.
Proof.
  intros c s c' H; induction H; intros w T Hc.
  - exact Hc.
  - (* RW1 *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [ts [Hw [HC [Hs HT]]]]]]].
    inversion Hs; subst.
    exists (w1 ++ w0), w3, (Node tC t), ts0.
    repeat split.
    + rewrite Hw. apply app_assoc.
    + eapply c_bin; eauto.
    + assumption.
  - (* RW2 *)
    destruct (IHderives w T Hc) as [ts [Hs HT]].
    exists [a], (s ++ w), (Leaf a), ts.
    repeat split; auto. apply c_term; assumption.
  - (* RW3 *)
    destruct (IHderives2 w T Hc) as [ts [Hs HT]].
    assert (Hsub : content ([], FNT B) (s1 ++ []) tB).
    { apply IHderives1. exists []. split; [constructor | reflexivity]. }
    destruct Hsub as [w1 [w2 [tA [ts' [Hw [HB [Hn HT']]]]]]].
    inversion Hn; subst. simpl in *. rewrite !app_nil_r in Hw. subst.
    exists (tA :: ts). split.
    + rewrite <- app_assoc. constructor; assumption.
    + reflexivity.
Qed.

Lemma path_to_cfg : forall A w t,
  derives ([], FNT A) w ([], FT t) -> cfg_der A w t.
Proof.
  intros A w t H.
  assert (Hc : content ([], FNT A) (w ++ []) t).
  { apply (derives_content _ _ _ H). exists []. split; [constructor | reflexivity]. }
  destruct Hc as [w1 [w2 [tA [ts [Hw [HA [Hn HT]]]]]]].
  inversion Hn; subst. rewrite !app_nil_r in *. simpl. subst. exact HA.
Qed.

(* Theorem 1 (strong form): the items reachable from  [] : A  with an
   empty final stack are exactly the derivation trees of G_P, and the
   emitted string is their yield (words are emitted in surface order). *)
Theorem path_cfg_equivalence : forall A w t,
  derives ([], FNT A) w ([], FT t) <-> cfg_der A w t.
Proof.
  split; [apply path_to_cfg | intro H; apply (cfg_to_path _ _ _ H [])].
Qed.

Corollary incremental_order : forall A w t,
  derives ([], FNT A) w ([], FT t) -> yield t = w.
Proof.
  intros. apply (cfg_der_yield A). apply path_to_cfg. assumption.
Qed.

Corollary weak_equivalence : forall S w, pg_language S w <-> cfg_language S w.
Proof.
  intros S w; split; intros [t H]; exists t; apply path_cfg_equivalence; exact H.
Qed.

End PathGrammars.

(* -------------------------------------------------------------- *)
(* From an arbitrary CFG in Chomsky normal form to a path grammar.  *)
(* -------------------------------------------------------------- *)
Section FromCNF.

Variables terminal nonterminal : Type.

Inductive cnf_rule : Type :=
  | BinR  : nonterminal -> nonterminal -> nonterminal -> cnf_rule  (* A -> B C *)
  | TermR : nonterminal -> terminal -> cnf_rule.                    (* A -> a   *)

Variable G : list cnf_rule.

Inductive cnf_der : nonterminal -> list terminal -> term terminal -> Prop :=
  | n_term : forall A a, In (TermR A a) G -> cnf_der A [a] (Leaf _ a)
  | n_bin : forall A B C w1 w2 t1 t2,
      In (BinR A B C) G -> cnf_der B w1 t1 -> cnf_der C w2 t2 ->
      cnf_der A (w1 ++ w2) (Node _ t1 t2).

(* Canonical translation:  A -> B C   becomes   A -> [C] B. *)
Definition tr (r : cnf_rule) : prule terminal nonterminal :=
  match r with
  | BinR A B C => PRule _ _ A C B
  | TermR A a => TRule _ _ A a
  end.

Definition PG := map tr G.

Lemma in_tr_bin : forall A B C,
  In (PRule _ _ A C B) PG <-> In (BinR A B C) G.
Proof.
  intros; unfold PG; rewrite in_map_iff; split.
  - intros [r [Hr Hin]]; destruct r; simpl in Hr; inversion Hr; subst; assumption.
  - intro H; exists (BinR A B C); split; [reflexivity | assumption].
Qed.

Lemma in_tr_term : forall A a,
  In (TRule _ _ A a) PG <-> In (TermR A a) G.
Proof.
  intros; unfold PG; rewrite in_map_iff; split.
  - intros [r [Hr Hin]]; destruct r; simpl in Hr; inversion Hr; subst; assumption.
  - intro H; exists (TermR A a); split; [reflexivity | assumption].
Qed.

Lemma cnf_iff_cfg : forall A w t, cnf_der A w t <-> cfg_der _ _ PG A w t.
Proof.
  split; intro H; induction H.
  - apply c_term. apply in_tr_term. assumption.
  - eapply c_bin; eauto. apply in_tr_bin. assumption.
  - apply n_term. apply in_tr_term. assumption.
  - eapply n_bin; eauto. apply in_tr_bin. assumption.
Qed.

(* Every CNF grammar G and its canonical path grammar P(G) generate
   the same strings and the same derivation trees. *)
Theorem cnf_path_equivalence : forall S w t,
  cnf_der S w t <-> derives _ _ PG ([], FNT _ _ S) w ([], FT _ _ t).
Proof.
  intros. rewrite cnf_iff_cfg. symmetry. apply path_cfg_equivalence.
Qed.

End FromCNF.
