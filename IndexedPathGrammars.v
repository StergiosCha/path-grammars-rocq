(* ===================================================================== *)
(*  Indexed Path Grammars and Linear Indexed Grammars                     *)
(*                                                                       *)
(*  An indexed path grammar derives exactly the derivation trees, and     *)
(*  hence exactly the strings, of the linear indexed grammar read off     *)
(*  from its rules; conversely every LIG in normal form is obtained in    *)
(*  this way from its canonical indexed path grammar.                     *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc IndexedPathGrammars.v).                  *)
(* ===================================================================== *)

Require Import List.
Import ListNotations.

Section IPG.

Variables terminal nonterminal index : Type.

(* Index stacks are lists with the top element at the head. *)
Definition cat : Type := (nonterminal * list index)%type.

(* ---------------------------------------------------------------- *)
(* Indexed path grammar rules                                        *)
(*   IBinP A B C   :  A[..] -> [B[]] C[..]   path daughter inherits   *)
(*   IBinD A B C   :  A[..] -> [B[..]] C[]   deferred daughter inherits*)
(*   IPush A i C   :  A[..] -> C[..i]                                *)
(*   IPop A i C    :  A[..i] -> C[..]                                *)
(*   IChain A C    :  A[..] -> C[..]                                 *)
(*   ITerm A o     :  A[] -> a   (o = Some a)  or  A[] -> eps (None) *)
(* ---------------------------------------------------------------- *)
Inductive irule : Type :=
  | IBinP : nonterminal -> nonterminal -> nonterminal -> irule
  | IBinD : nonterminal -> nonterminal -> nonterminal -> irule
  | IPush : nonterminal -> index -> nonterminal -> irule
  | IPop : nonterminal -> index -> nonterminal -> irule
  | IChain : nonterminal -> nonterminal -> irule
  | ITerm : nonterminal -> option terminal -> irule.

Inductive term : Type :=
  | Leaf : option terminal -> term
  | Node : term -> term -> term.

Definition emit (o : option terminal) : list terminal :=
  match o with Some a => [a] | None => [] end.

Fixpoint yield (t : term) : list terminal :=
  match t with
  | Leaf o => emit o
  | Node l r => yield l ++ yield r
  end.

Inductive focus : Type :=
  | FNT : cat -> focus
  | FT : term -> focus.

Definition item : Type := (list cat * focus)%type.

Variable R : list irule.

Inductive derives : item -> list terminal -> item -> Prop :=
  | d_refl : forall c, derives c [] c
  | d_binp : forall X A B C ix s c',
      In (IBinP A B C) R ->
      derives ((B, []) :: X, FNT (C, ix)) s c' ->
      derives (X, FNT (A, ix)) s c'
  | d_bind : forall X A B C ix s c',
      In (IBinD A B C) R ->
      derives ((B, ix) :: X, FNT (C, [])) s c' ->
      derives (X, FNT (A, ix)) s c'
  | d_push : forall X A i C ix s c',
      In (IPush A i C) R ->
      derives (X, FNT (C, i :: ix)) s c' ->
      derives (X, FNT (A, ix)) s c'
  | d_pop : forall X A i C ix s c',
      In (IPop A i C) R ->
      derives (X, FNT (C, ix)) s c' ->
      derives (X, FNT (A, i :: ix)) s c'
  | d_chain : forall X A C ix s c',
      In (IChain A C) R ->
      derives (X, FNT (C, ix)) s c' ->
      derives (X, FNT (A, ix)) s c'
  | d_term : forall X A o s c',
      In (ITerm A o) R ->
      derives (X, FT (Leaf o)) s c' ->
      derives (X, FNT (A, [])) (emit o ++ s) c'
  | d_pop3 : forall X B t tB s1 s2 c',
      derives ([], FNT B) s1 ([], FT tB) ->
      derives (X, FT (Node t tB)) s2 c' ->
      derives (B :: X, FT t) (s1 ++ s2) c'.

Definition ipg_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, derives ([], FNT (S, [])) w ([], FT t).

(* The linear indexed grammar G_P read off from P (left daughter first):
     A[..] -> [B[]] C[..]   becomes   A[..] -> C[..] B[]
     A[..] -> [B[..]] C[]   becomes   A[..] -> C[] B[..]
   lig_der (A, ix) w t : A[ix] derives w with derivation tree t.     *)
Inductive lig_der : cat -> list terminal -> term -> Prop :=
  | l_binp : forall A B C ix w1 w2 t1 t2,
      In (IBinP A B C) R ->
      lig_der (C, ix) w1 t1 -> lig_der (B, []) w2 t2 ->
      lig_der (A, ix) (w1 ++ w2) (Node t1 t2)
  | l_bind : forall A B C ix w1 w2 t1 t2,
      In (IBinD A B C) R ->
      lig_der (C, []) w1 t1 -> lig_der (B, ix) w2 t2 ->
      lig_der (A, ix) (w1 ++ w2) (Node t1 t2)
  | l_push : forall A i C ix w t,
      In (IPush A i C) R -> lig_der (C, i :: ix) w t -> lig_der (A, ix) w t
  | l_pop : forall A i C ix w t,
      In (IPop A i C) R -> lig_der (C, ix) w t -> lig_der (A, i :: ix) w t
  | l_chain : forall A C ix w t,
      In (IChain A C) R -> lig_der (C, ix) w t -> lig_der (A, ix) w t
  | l_term : forall A o,
      In (ITerm A o) R -> lig_der (A, []) (emit o) (Leaf o).

Definition lig_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, lig_der (S, []) w t.

Lemma lig_der_yield : forall c w t, lig_der c w t -> yield t = w.
Proof. intros c w t H; induction H; simpl; congruence. Qed.

Lemma derives_trans : forall c1 s1 c2 s2 c3,
  derives c1 s1 c2 -> derives c2 s2 c3 -> derives c1 (s1 ++ s2) c3.
Proof.
  intros c1 s1 c2 s2 c3 H1 H2. induction H1.
  - exact H2.
  - eapply d_binp; eauto.
  - eapply d_bind; eauto.
  - eapply d_push; eauto.
  - eapply d_pop; eauto.
  - eapply d_chain; eauto.
  - rewrite <- app_assoc. eapply d_term; eauto.
  - rewrite <- app_assoc. eapply d_pop3; eauto.
Qed.

(* ---------------- Completeness:  LIG  ==>  IPG -------------------- *)

Lemma lig_to_ipg : forall c w t,
  lig_der c w t -> forall X, derives (X, FNT c) w (X, FT t).
Proof.
  intros c w t H; induction H; intros X.
  - eapply d_binp; [eassumption |].
    eapply derives_trans; [apply IHlig_der1 |].
    rewrite <- (app_nil_r w2). eapply d_pop3; [apply IHlig_der2 | apply d_refl].
  - eapply d_bind; [eassumption |].
    eapply derives_trans; [apply IHlig_der1 |].
    rewrite <- (app_nil_r w2). eapply d_pop3; [apply IHlig_der2 | apply d_refl].
  - eapply d_push; eauto.
  - eapply d_pop; eauto.
  - eapply d_chain; eauto.
  - rewrite <- (app_nil_r (emit o)). eapply d_term; [eassumption | apply d_refl].
Qed.

(* ---------------- Soundness:  IPG  ==>  LIG ----------------------- *)

Inductive lig_ders : list cat -> list terminal -> list term -> Prop :=
  | ls_nil : lig_ders [] [] []
  | ls_cons : forall c X w1 w2 t ts,
      lig_der c w1 t -> lig_ders X w2 ts -> lig_ders (c :: X) (w1 ++ w2) (t :: ts).

Fixpoint attach (t : term) (ts : list term) : term :=
  match ts with
  | [] => t
  | u :: us => attach (Node t u) us
  end.

Definition content (c : item) (w : list terminal) (T : term) : Prop :=
  match c with
  | (X, FNT a) => exists w1 w2 ta ts,
      w = w1 ++ w2 /\ lig_der a w1 ta /\ lig_ders X w2 ts /\ T = attach ta ts
  | (X, FT t) => exists ts, lig_ders X w ts /\ T = attach t ts
  end.

Ltac unary_case IH w T Hc ctor :=
  destruct (IH w T Hc) as [w1 [w2 [ta [ts [Hw [Ha [Hs HT]]]]]]];
  exists w1, w2, ta, ts; repeat split; auto; eapply ctor; eauto.

Lemma derives_content : forall c s c',
  derives c s c' -> forall w T, content c' w T -> content c (s ++ w) T.
Proof.
  intros c s c' H; induction H; intros w T Hc.
  - exact Hc.
  - destruct (IHderives w T Hc) as [w1 [w2 [tC [ts [Hw [HC [Hs HT]]]]]]].
    inversion Hs; subst.
    exists (w1 ++ w0), w3, (Node tC t), ts0. repeat split.
    + rewrite Hw. apply app_assoc.
    + eapply l_binp; eauto.
    + assumption.
  - destruct (IHderives w T Hc) as [w1 [w2 [tC [ts [Hw [HC [Hs HT]]]]]]].
    inversion Hs; subst.
    exists (w1 ++ w0), w3, (Node tC t), ts0. repeat split.
    + rewrite Hw. apply app_assoc.
    + eapply l_bind; eauto.
    + assumption.
  - unary_case IHderives w T Hc l_push.
  - unary_case IHderives w T Hc l_pop.
  - unary_case IHderives w T Hc l_chain.
  - destruct (IHderives w T Hc) as [ts [Hs HT]].
    exists (emit o), (s ++ w), (Leaf o), ts.
    repeat split; auto.
    + symmetry. apply app_assoc.
    + apply l_term; assumption.
  - destruct (IHderives2 w T Hc) as [ts [Hs HT]].
    assert (Hsub : content ([], FNT B) (s1 ++ []) tB).
    { apply IHderives1. exists []. split; [constructor | reflexivity]. }
    destruct Hsub as [w1 [w2 [ta [ts' [Hw [HB [Hn HT']]]]]]].
    inversion Hn; subst. rewrite !app_nil_r in *. simpl in *. subst.
    exists (ta :: ts). split.
    + rewrite <- app_assoc. constructor; assumption.
    + reflexivity.
Qed.

Lemma ipg_to_lig : forall c w t,
  derives ([], FNT c) w ([], FT t) -> lig_der c w t.
Proof.
  intros c w t H.
  assert (Hc : content ([], FNT c) (w ++ []) t).
  { apply (derives_content _ _ _ H). exists []. split; [constructor | reflexivity]. }
  destruct Hc as [w1 [w2 [ta [ts [Hw [Ha [Hn HT]]]]]]].
  inversion Hn; subst. rewrite !app_nil_r in *. simpl. subst. exact Ha.
Qed.

(* IPG/LIG correspondence (strong form). *)
Theorem ipg_lig_equivalence : forall c w t,
  derives ([], FNT c) w ([], FT t) <-> lig_der c w t.
Proof.
  split; [apply ipg_to_lig | intro H; apply (lig_to_ipg _ _ _ H [])].
Qed.

Corollary ipg_incremental_order : forall c w t,
  derives ([], FNT c) w ([], FT t) -> yield t = w.
Proof. intros. eapply lig_der_yield. apply ipg_to_lig. eassumption. Qed.

(* Item completion for IPGs. *)
Corollary ipg_item_completion : forall c s T,
  derives c s ([], FT T) -> content c s T.
Proof.
  intros c s T H. rewrite <- (app_nil_r s).
  apply (derives_content _ _ _ H). exists []. split; [constructor | reflexivity].
Qed.

Corollary ipg_weak_equivalence : forall S w, ipg_language S w <-> lig_language S w.
Proof.
  intros S w; split; intros [t H]; exists t; apply ipg_lig_equivalence; exact H.
Qed.

(* ===================================================================== *)
(*  Flattened derivations and nested item completion for IPGs.           *)
(* ===================================================================== *)

Inductive frame : Type := Fr : list cat -> term -> frame.

Definition config : Type := (list frame * item)%type.

Inductive mstep : config -> list terminal -> config -> Prop :=
  | m_binp : forall F X A B C ix, In (IBinP A B C) R ->
      mstep (F, (X, FNT (A, ix))) [] (F, ((B, []) :: X, FNT (C, ix)))
  | m_bind : forall F X A B C ix, In (IBinD A B C) R ->
      mstep (F, (X, FNT (A, ix))) [] (F, ((B, ix) :: X, FNT (C, [])))
  | m_push : forall F X A i C ix, In (IPush A i C) R ->
      mstep (F, (X, FNT (A, ix))) [] (F, (X, FNT (C, i :: ix)))
  | m_pop : forall F X A i C ix, In (IPop A i C) R ->
      mstep (F, (X, FNT (A, i :: ix))) [] (F, (X, FNT (C, ix)))
  | m_chain : forall F X A C ix, In (IChain A C) R ->
      mstep (F, (X, FNT (A, ix))) [] (F, (X, FNT (C, ix)))
  | m_term : forall F X A o, In (ITerm A o) R ->
      mstep (F, (X, FNT (A, []))) (emit o) (F, (X, FT (Leaf o)))
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

Lemma ms_one : forall k1 k2 s k3, mstep k1 [] k2 -> msteps k2 s k3 -> msteps k1 s k3.
Proof. intros. change s with ([] ++ s). eapply ms_step; eauto. Qed.

Lemma derives_to_machine : forall c s c',
  derives c s c' -> forall F, msteps (F, c) s (F, c').
Proof.
  intros c s c' H; induction H; intros F.
  - apply ms_refl.
  - eapply ms_one; [apply m_binp; eassumption | apply IHderives].
  - eapply ms_one; [apply m_bind; eassumption | apply IHderives].
  - eapply ms_one; [apply m_push; eassumption | apply IHderives].
  - eapply ms_one; [apply m_pop; eassumption | apply IHderives].
  - eapply ms_one; [apply m_chain; eassumption | apply IHderives].
  - eapply ms_step; [apply m_term; eassumption | apply IHderives].
  - eapply ms_one; [apply m_call |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret | apply IHderives2].
Qed.

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

Lemma local_lift : forall c s c',
  derives c s c' -> forall F w T, gcontent F c' w T -> gcontent F c (s ++ w) T.
Proof. intros c s c' H. apply gcontent_lift. apply derives_content. exact H. Qed.

Lemma content_nil_nt : forall b s tB, content ([], FNT b) s tB -> lig_der b s tB.
Proof.
  intros b s tB [w1 [w2 [ta [ts [Hw [Ha [Hn HT]]]]]]].
  inversion Hn; subst. rewrite !app_nil_r in *. simpl. exact Ha.
Qed.

Lemma mstep_gcontent : forall k s k',
  mstep k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; inversion H; subst; cbn [fst snd]; intros w T Hg.
  - eapply local_lift; [eapply d_binp; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_bind; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_push; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_pop; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_chain; [exact H0 | apply d_refl] | exact Hg].
  - rewrite <- (app_nil_r (emit o)) at 1.
    eapply local_lift; [eapply d_term; [exact H0 | apply d_refl] | exact Hg].
  - simpl in Hg. destruct Hg as [w1 [w2 [tB [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' [ts [Hs HT]]. exists (tB :: ts). split.
    + constructor; [apply content_nil_nt; exact Hc | exact Hs].
    + exact HT.
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

(* Nested item completion for IPGs (Corollary 11). *)
Corollary ipg_nested_item_completion : forall k s T,
  msteps k s ([], ([], FT T)) -> gcontent (fst k) (snd k) s T.
Proof.
  intros k s T H. rewrite <- (app_nil_r s).
  apply (msteps_gcontent _ _ _ H). simpl. exists []. split; [constructor | reflexivity].
Qed.

Theorem ipg_machine_equivalence : forall c w t,
  msteps ([], ([], FNT c)) w ([], ([], FT t)) <-> derives ([], FNT c) w ([], FT t).
Proof.
  intros c w t; split.
  - intro H. apply ipg_lig_equivalence. apply content_nil_nt.
    exact (ipg_nested_item_completion _ _ _ H).
  - intro H. exact (derives_to_machine _ _ _ H []).
Qed.


End IPG.

(* -------------------------------------------------------------- *)
(* From a LIG in normal form (written left daughter first) to its   *)
(* canonical indexed path grammar.                                  *)
(* -------------------------------------------------------------- *)
Section FromLIG.

Variables terminal nonterminal index : Type.

Inductive lrule : Type :=
  | LInhL : nonterminal -> nonterminal -> nonterminal -> lrule  (* A[..] -> B[..] C[] *)
  | LInhR : nonterminal -> nonterminal -> nonterminal -> lrule  (* A[..] -> B[] C[..] *)
  | LPush : nonterminal -> index -> nonterminal -> lrule        (* A[..] -> B[..i]    *)
  | LPop : nonterminal -> index -> nonterminal -> lrule         (* A[..i] -> B[..]    *)
  | LChain : nonterminal -> nonterminal -> lrule                (* A[..] -> B[..]     *)
  | LTerm : nonterminal -> option terminal -> lrule.            (* A[] -> a | eps     *)

Variable G : list lrule.

Notation cat := (cat nonterminal index).
Notation term := (term terminal).

Inductive nf_der : cat -> list terminal -> term -> Prop :=
  | n_inhl : forall A B C ix w1 w2 t1 t2,
      In (LInhL A B C) G -> nf_der (B, ix) w1 t1 -> nf_der (C, []) w2 t2 ->
      nf_der (A, ix) (w1 ++ w2) (Node _ t1 t2)
  | n_inhr : forall A B C ix w1 w2 t1 t2,
      In (LInhR A B C) G -> nf_der (B, []) w1 t1 -> nf_der (C, ix) w2 t2 ->
      nf_der (A, ix) (w1 ++ w2) (Node _ t1 t2)
  | n_push : forall A i B ix w t,
      In (LPush A i B) G -> nf_der (B, i :: ix) w t -> nf_der (A, ix) w t
  | n_pop : forall A i B ix w t,
      In (LPop A i B) G -> nf_der (B, ix) w t -> nf_der (A, i :: ix) w t
  | n_chain : forall A B ix w t,
      In (LChain A B) G -> nf_der (B, ix) w t -> nf_der (A, ix) w t
  | n_term : forall A o,
      In (LTerm A o) G -> nf_der (A, []) (emit _ o) (Leaf _ o).

(* Canonical translation: the left daughter becomes the path daughter. *)
Definition tr (r : lrule) : irule terminal nonterminal index :=
  match r with
  | LInhL A B C => IBinP _ _ _ A C B
  | LInhR A B C => IBinD _ _ _ A C B
  | LPush A i B => IPush _ _ _ A i B
  | LPop A i B => IPop _ _ _ A i B
  | LChain A B => IChain _ _ _ A B
  | LTerm A o => ITerm _ _ _ A o
  end.

Definition IP := map tr G.

(* The translations between normal-form LIGs and IPGs are mutually inverse. *)
Definition untr (r : irule terminal nonterminal index) : lrule :=
  match r with
  | IBinP _ _ _ A C B => LInhL A B C
  | IBinD _ _ _ A C B => LInhR A B C
  | IPush _ _ _ A i B => LPush A i B
  | IPop _ _ _ A i B => LPop A i B
  | IChain _ _ _ A B => LChain A B
  | ITerm _ _ _ A o => LTerm A o
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


Lemma in_IP : forall r, In r G -> In (tr r) IP.
Proof. intros r H. unfold IP. apply in_map. exact H. Qed.

Ltac from_IP H :=
  unfold IP in H; apply in_map_iff in H;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hin := fresh "Hin" in
  destruct H as [r [Hr Hin]]; destruct r; simpl in Hr; inversion Hr; subst; exact Hin.

Lemma nf_iff_lig : forall c w t, nf_der c w t <-> lig_der _ _ _ IP c w t.
Proof.
  split; intro H; induction H.
  - eapply l_binp; eauto. exact (in_IP _ H).
  - eapply l_bind; eauto. exact (in_IP _ H).
  - eapply l_push; eauto. exact (in_IP _ H).
  - eapply l_pop; eauto. exact (in_IP _ H).
  - eapply l_chain; eauto. exact (in_IP _ H).
  - apply l_term. exact (in_IP _ H).
  - eapply n_inhl; eauto. from_IP H.
  - eapply n_inhr; eauto. from_IP H.
  - eapply n_push; eauto. from_IP H.
  - eapply n_pop; eauto. from_IP H.
  - eapply n_chain; eauto. from_IP H.
  - apply n_term. from_IP H.
Qed.

(* Every normal-form LIG and its canonical indexed path grammar derive the
   same strings with the same derivation trees. *)
Theorem lig_ipg_equivalence : forall S w t,
  nf_der (S, []) w t <-> derives _ _ _ IP ([], FNT _ _ _ (S, [])) w ([], FT _ _ _ t).
Proof.
  intros. rewrite nf_iff_lig. symmetry. apply ipg_lig_equivalence.
Qed.

End FromLIG.
