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

(* Path grammar/CFG correspondence (strong form): the items reachable from  [] : A  with an
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

(* Item completion: every item on a derivation ending in the
   final term T can be completed to T by attaching trees for its deferred
   daughters, i.e. T arises from the item's partial term by filling its
   open leaves. *)
Corollary item_completion : forall c s T,
  derives c s ([], FT T) -> content c s T.
Proof.
  intros c s T H. rewrite <- (app_nil_r s).
  apply (derives_content _ _ _ H). exists []. split; [constructor | reflexivity].
Qed.

(* ===================================================================== *)
(*  Flattened derivations and nested item completion.                    *)
(*                                                                       *)
(*  Flattening the sub-derivations of RW3 gives a stack machine whose    *)
(*  configurations are a list of suspended enclosing items (frames) and  *)
(*  a current item.  A frame Fr X t is an enclosing item <B, X> : t      *)
(*  waiting for the term derived from B.  The machine is the predictive  *)
(*  pushdown automaton of Remark 1.                                      *)
(* ===================================================================== *)

Inductive frame : Type := Fr : list nonterminal -> term -> frame.

Definition config : Type := (list frame * item)%type.

Inductive mstep : config -> list terminal -> config -> Prop :=
  | m_rw1 : forall F X A B C,
      In (PRule A B C) R -> mstep (F, (X, FNT A)) [] (F, (B :: X, FNT C))
  | m_rw2 : forall F X A a,
      In (TRule A a) R -> mstep (F, (X, FNT A)) [a] (F, (X, FT (Leaf a)))
  | m_call : forall F X B t,
      mstep (F, (B :: X, FT t)) [] (Fr X t :: F, ([], FNT B))
  | m_ret : forall F X t tB,
      mstep (Fr X t :: F, ([], FT tB)) [] (F, (X, FT (Node t tB))).

Inductive msteps : config -> list terminal -> config -> Prop :=
  | ms_refl : forall k, msteps k [] k
  | ms_step : forall k1 s1 k2 s2 k3,
      mstep k1 s1 k2 -> msteps k2 s2 k3 -> msteps k1 (s1 ++ s2) k3.

Lemma msteps_trans : forall k1 s1 k2 s2 k3,
  msteps k1 s1 k2 -> msteps k2 s2 k3 -> msteps k1 (s1 ++ s2) k3.
Proof.
  intros k1 s1 k2 s2 k3 H1 H2. induction H1.
  - exact H2.
  - rewrite <- app_assoc. eapply ms_step; eauto.
Qed.

Lemma derives_to_machine : forall c s c',
  derives c s c' -> forall F, msteps (F, c) s (F, c').
Proof.
  intros c s c' H; induction H; intros F.
  - apply ms_refl.
  - change s with ([] ++ s). eapply ms_step; [apply m_rw1; eassumption | apply IHderives].
  - change (a :: s) with ([a] ++ s). eapply ms_step; [apply m_rw2; eassumption | apply IHderives].
  - change (s1 ++ s2) with ([] ++ (s1 ++ s2)).
    eapply ms_step; [apply m_call |].
    eapply msteps_trans; [apply IHderives1 |].
    change s2 with ([] ++ s2).
    eapply ms_step; [apply m_ret | apply IHderives2].
Qed.

(* Global completion: the current item completes to the term of its
   sub-derivation, which is plugged into the enclosing frame, and so on
   outwards.  This is the composition of nested items with their
   enclosing items in Corollary 4. *)
Fixpoint gcontent (F : list frame) (c : item) (w : list terminal) (T : term) : Prop :=
  match F with
  | [] => content c w T
  | Fr X t :: F' => exists w1 w2 tB,
      w = w1 ++ w2 /\ content c w1 tB /\ gcontent F' (X, FT (Node t tB)) w2 T
  end.

Lemma gcontent_lift : forall c c' s,
  (forall w T, content c' w T -> content c (s ++ w) T) ->
  forall F w T, gcontent F c' w T -> gcontent F c (s ++ w) T.
Proof.
  intros c c' s Hl F w T. destruct F as [| [X t] F']; simpl.
  - apply Hl.
  - intros [w1 [w2 [tB [E [Hc Hg]]]]].
    exists (s ++ w1), w2, tB. repeat split; auto.
    rewrite E. apply app_assoc.
Qed.

Lemma content_nil_nt : forall B s tB, content ([], FNT B) s tB -> cfg_der B s tB.
Proof.
  intros B s tB [w1 [w2 [tA [ts [Hw [HA [Hn HT]]]]]]].
  inversion Hn; subst. rewrite !app_nil_r in *. simpl. exact HA.
Qed.

Lemma content_push : forall B X t w1 tB,
  cfg_der B w1 tB ->
  forall w T, content (X, FT (Node t tB)) w T -> content (B :: X, FT t) (w1 ++ w) T.
Proof.
  intros B X t w1 tB HB w T [ts [Hs HT]].
  exists (tB :: ts). split; [constructor; assumption | exact HT].
Qed.

Lemma mstep_gcontent : forall k s k',
  mstep k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; inversion H; subst; cbn [fst snd]; intros w T Hg.
  - eapply gcontent_lift; [| exact Hg].
    intros w' T' Hc. apply (derives_content _ _ _ (d_rw1 _ _ _ _ _ _ H0 (d_refl _))). exact Hc.
  - eapply gcontent_lift with (s := [a]); [| exact Hg].
    intros w' T' Hc. apply (derives_content _ _ _ (d_rw2 _ _ _ _ _ H0 (d_refl _))). exact Hc.
  - simpl in Hg. destruct Hg as [w1 [w2 [tB [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    apply content_push. apply content_nil_nt. exact Hc.
  - simpl. exists [], w, tB. repeat split.
    + exists []. split; [constructor | reflexivity].
    + exact Hg.
Qed.

Lemma msteps_gcontent : forall k s k',
  msteps k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; induction H; intros w T Hg.
  - exact Hg.
  - rewrite <- app_assoc. eapply mstep_gcontent; [exact H | apply IHmsteps; exact Hg].
Qed.

(* Nested item completion: every configuration on a run that ends in the
   final term T completes to T through its frames. *)
Corollary nested_item_completion : forall k s T,
  msteps k s ([], ([], FT T)) -> gcontent (fst k) (snd k) s T.
Proof.
  intros k s T H. rewrite <- (app_nil_r s).
  apply (msteps_gcontent _ _ _ H). simpl. exists []. split; [constructor | reflexivity].
Qed.

(* The flattened machine and the nested rewrite semantics agree. *)
Theorem machine_equivalence : forall A w t,
  msteps ([], ([], FNT A)) w ([], ([], FT t)) <-> derives ([], FNT A) w ([], FT t).
Proof.
  intros A w t; split.
  - intro H. apply path_cfg_equivalence.
    apply content_nil_nt. exact (nested_item_completion _ _ _ H).
  - intro H. exact (derives_to_machine _ _ _ H []).
Qed.

(* Proposition 1 (shape of derivations), recursive form: a derivation
   from A either scans one word, or expands A -> [B]C, derives C, and
   then derives the deferred B.  (That foci are single non-terminals or
   terms, and which rules apply to which, is enforced by the type of
   foci and by the constructors of derives.) *)
Lemma derivation_shape : forall A w t,
  derives ([], FNT A) w ([], FT t) ->
  (exists a, In (TRule A a) R /\ w = [a] /\ t = Leaf a) \/
  (exists B C w1 w2 t1 t2, In (PRule A B C) R /\
     derives ([], FNT C) w1 ([], FT t1) /\ derives ([], FNT B) w2 ([], FT t2) /\
     w = w1 ++ w2 /\ t = Node t1 t2).
Proof.
  intros A w t H. apply path_cfg_equivalence in H. inversion H; subst.
  - left. eauto.
  - right. exists B, C, w1, w2, t1, t2.
    repeat split; auto; apply path_cfg_equivalence; assumption.
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

(* The two translations are mutually inverse. *)
Definition untr (r : prule terminal nonterminal) : cnf_rule :=
  match r with
  | PRule _ _ A B C => BinR A C B
  | TRule _ _ A a => TermR A a
  end.

Lemma untr_tr : forall r, untr (tr r) = r.
Proof. intros []; reflexivity. Qed.

Lemma tr_untr : forall r, tr (untr r) = r.
Proof. intros []; reflexivity. Qed.

Corollary translations_inverse : forall P,
  map untr (map tr G) = G /\ map tr (map untr P) = P.
Proof.
  intros P; split; rewrite map_map.
  - transitivity (map (fun x => x) G); [apply map_ext; apply untr_tr | apply map_id].
  - transitivity (map (fun x => x) P); [apply map_ext; apply tr_untr | apply map_id].
Qed.



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
