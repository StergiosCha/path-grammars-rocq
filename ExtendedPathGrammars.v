(* ===================================================================== *)
(*  Extended Path Grammars (slash categories + LINK):                     *)
(*  their string languages are context-free.                              *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc ExtendedPathGrammars.v).                 *)
(* ===================================================================== *)

Require Import List.
Import ListNotations.

Section Extended.

Variables terminal nonterminal : Type.

Inductive rule : Type :=
  | PRule : nonterminal -> nonterminal -> nonterminal -> rule
      (* A -> [B] C *)
  | TRule : nonterminal -> terminal -> rule
      (* A -> a *)
  | TopRule : nonterminal -> nonterminal -> rule
      (* TopRule A D : (A, D) in TOP, a D may be fronted out of an A *)
  | LRule : nonterminal -> nonterminal -> nonterminal -> nonterminal -> rule.
      (* LRule A D C B : A -> [LINK_D(C)] B *)

Inductive term : Type :=
  | Leaf : terminal -> term
  | Node : term -> term -> term
  | LinkT : term -> term.            (* a LINKed tree *)

(* Stack symbols: plain categories, slashed categories carrying the
   filler's term, and pending LINK sites. *)
Inductive ssym : Type :=
  | SNT : nonterminal -> ssym
  | SSlash : nonterminal -> nonterminal -> term -> ssym     (* B/D[alpha] *)
  | SLink : nonterminal -> nonterminal -> ssym.             (* LINK_D(C)  *)

Inductive focus : Type :=
  | FNT : nonterminal -> focus
  | FSlash : nonterminal -> nonterminal -> term -> focus    (* A/D[alpha] *)
  | FT : term -> focus.

Definition item : Type := (list ssym * focus)%type.

Variable R : list rule.

Inductive derives : item -> list terminal -> item -> Prop :=
  | d_refl : forall c, derives c [] c
  (* RW1 *)
  | d_rw1 : forall X A B C s c',
      In (PRule A B C) R ->
      derives (SNT B :: X, FNT C) s c' ->
      derives (X, FNT A) s c'
  (* RW2 *)
  | d_rw2 : forall X A a s c',
      In (TRule A a) R ->
      derives (X, FT (Leaf a)) s c' ->
      derives (X, FNT A) (a :: s) c'
  (* RW3, for plain and for slashed stack symbols *)
  | d_rw3 : forall X B t tB s1 s2 c',
      derives ([], FNT B) s1 ([], FT tB) ->
      derives (X, FT (Node t tB)) s2 c' ->
      derives (SNT B :: X, FT t) (s1 ++ s2) c'
  | d_rw3s : forall X B D al t tB s1 s2 c',
      derives ([], FSlash B D al) s1 ([], FT tB) ->
      derives (X, FT (Node t tB)) s2 c' ->
      derives (SSlash B D al :: X, FT t) (s1 ++ s2) c'
  (* RW4: slash introduction (fronting) *)
  | d_rw4 : forall X A D al s1 s2 c',
      In (TopRule A D) R ->
      derives ([], FNT D) s1 ([], FT al) ->
      derives (X, FSlash A D al) s2 c' ->
      derives (X, FNT A) (s1 ++ s2) c'
  (* RW5a/b: slash propagation into the deferred or the path daughter *)
  | d_rw5a : forall X A B C D al s c',
      In (PRule A B C) R ->
      derives (SSlash B D al :: X, FNT C) s c' ->
      derives (X, FSlash A D al) s c'
  | d_rw5b : forall X A B C D al s c',
      In (PRule A B C) R ->
      derives (SNT B :: X, FSlash C D al) s c' ->
      derives (X, FSlash A D al) s c'
  (* RW6: slash elimination; the filler's term fills the gap *)
  | d_rw6 : forall X D al s c',
      derives (X, FT al) s c' ->
      derives (X, FSlash D D al) s c'
  (* RW7: LINK introduction *)
  | d_rw7 : forall X A D C B s c',
      In (LRule A D C B) R ->
      derives (SLink D C :: X, FNT B) s c' ->
      derives (X, FNT A) s c'
  (* RW8: LINK resolution; the linked C is derived with a D-gap that is
     filled by a copy of the host term t *)
  | d_rw8 : forall X D C t tL s1 s2 c',
      derives ([], FSlash C D t) s1 ([], FT tL) ->
      derives (X, FT (Node t (LinkT tL))) s2 c' ->
      derives (SLink D C :: X, FT t) (s1 ++ s2) c'.

Definition epg_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, derives ([], FNT S) w ([], FT t).

(* ------------------------------------------------------------------ *)
(* The context-free grammar G-flat over the finite category set        *)
(*   N  u  { A/D | A, D in N }.                                        *)
(* ------------------------------------------------------------------ *)
Inductive cat : Type :=
  | CN : nonterminal -> cat
  | CS : nonterminal -> nonterminal -> cat.

Inductive gder : cat -> list terminal -> Prop :=
  | g_term : forall A a, In (TRule A a) R -> gder (CN A) [a]
  | g_bin : forall A B C w1 w2,
      In (PRule A B C) R -> gder (CN C) w1 -> gder (CN B) w2 ->
      gder (CN A) (w1 ++ w2)                       (* A -> C B       *)
  | g_top : forall A D w1 w2,
      In (TopRule A D) R -> gder (CN D) w1 -> gder (CS A D) w2 ->
      gder (CN A) (w1 ++ w2)                       (* A -> D A/D     *)
  | g_sa : forall A B C D w1 w2,
      In (PRule A B C) R -> gder (CN C) w1 -> gder (CS B D) w2 ->
      gder (CS A D) (w1 ++ w2)                     (* A/D -> C B/D   *)
  | g_sb : forall A B C D w1 w2,
      In (PRule A B C) R -> gder (CS C D) w1 -> gder (CN B) w2 ->
      gder (CS A D) (w1 ++ w2)                     (* A/D -> C/D B   *)
  | g_gap : forall D, gder (CS D D) []             (* D/D -> epsilon *)
  | g_link : forall A D C B w1 w2,
      In (LRule A D C B) R -> gder (CN B) w1 -> gder (CS C D) w2 ->
      gder (CN A) (w1 ++ w2).                      (* A -> B C/D     *)

Definition flat_language (S : nonterminal) (w : list terminal) : Prop :=
  gder (CN S) w.

Lemma derives_trans : forall c1 s1 c2 s2 c3,
  derives c1 s1 c2 -> derives c2 s2 c3 -> derives c1 (s1 ++ s2) c3.
Proof.
  intros c1 s1 c2 s2 c3 H1 H2.
  induction H1.
  - exact H2.
  - eapply d_rw1; eauto.
  - simpl. eapply d_rw2; eauto.
  - rewrite <- app_assoc. eapply d_rw3; eauto.
  - rewrite <- app_assoc. eapply d_rw3s; eauto.
  - rewrite <- app_assoc. eapply d_rw4; eauto.
  - eapply d_rw5a; eauto.
  - eapply d_rw5b; eauto.
  - eapply d_rw6; eauto.
  - eapply d_rw7; eauto.
  - rewrite <- app_assoc. eapply d_rw8; eauto.
Qed.

(* ---------------- Completeness:  G-flat  ==>  EPG ----------------- *)

Definition realisable (c : cat) (w : list terminal) (X : list ssym) : Prop :=
  match c with
  | CN A => exists t, derives (X, FNT A) w (X, FT t)
  | CS A D => forall al, exists t, derives (X, FSlash A D al) w (X, FT t)
  end.

Lemma flat_to_epg : forall c w, gder c w -> forall X, realisable c w X.
Proof.
  intros c w H; induction H; intros X; simpl in *.
  - exists (Leaf a). rewrite <- (app_nil_r [a]).
    eapply d_rw2; [eassumption | apply d_refl].
  - destruct (IHgder1 (SNT B :: X)) as [t1 K1].
    destruct (IHgder2 []) as [t2 K2].
    exists (Node t1 t2). eapply d_rw1; [eassumption |].
    eapply derives_trans; [exact K1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [exact K2 | apply d_refl].
  - destruct (IHgder1 []) as [t1 K1].
    destruct (IHgder2 X t1) as [t2 K2].
    exists t2. eapply d_rw4; eassumption.
  - intro al.
    destruct (IHgder2 [] al) as [t2 K2].
    destruct (IHgder1 (SSlash B D al :: X)) as [t1 K1].
    exists (Node t1 t2). eapply d_rw5a; [eassumption |].
    eapply derives_trans; [exact K1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3s; [exact K2 | apply d_refl].
  - intro al.
    destruct (IHgder1 (SNT B :: X) al) as [t1 K1].
    destruct (IHgder2 []) as [t2 K2].
    exists (Node t1 t2). eapply d_rw5b; [eassumption |].
    eapply derives_trans; [exact K1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [exact K2 | apply d_refl].
  - intro al. exists al. apply d_rw6. apply d_refl.
  - destruct (IHgder1 (SLink D C :: X)) as [t1 K1].
    destruct (IHgder2 [] t1) as [t2 K2].
    exists (Node t1 (LinkT t2)). eapply d_rw7; [eassumption |].
    eapply derives_trans; [exact K1 |].
    rewrite <- (app_nil_r w2). eapply d_rw8; [exact K2 | apply d_refl].
Qed.

(* ---------------- Soundness:  EPG  ==>  G-flat --------------------- *)

Definition scat (x : ssym) : cat :=
  match x with
  | SNT B => CN B
  | SSlash B D _ => CS B D
  | SLink D C => CS C D
  end.

Inductive gders : list cat -> list terminal -> Prop :=
  | gs_nil : gders [] []
  | gs_cons : forall c cs w1 w2,
      gder c w1 -> gders cs w2 -> gders (c :: cs) (w1 ++ w2).

(* What remains to be derived from an item, as a list of categories. *)
Definition pending (c : item) : list cat :=
  match c with
  | (X, FNT A) => CN A :: map scat X
  | (X, FSlash A D _) => CS A D :: map scat X
  | (X, FT _) => map scat X
  end.

Lemma gders_one : forall c w, gders [c] w -> gder c w.
Proof.
  intros c w H. inversion H; subst. inversion H4; subst.
  rewrite app_nil_r. assumption.
Qed.

Lemma gders_inv : forall c cs w, gders (c :: cs) w ->
  exists w1 w2, w = w1 ++ w2 /\ gder c w1 /\ gders cs w2.
Proof.
  intros c cs w H. inversion H; subst. eauto.
Qed.

Lemma sub_der : forall f s t,
  (forall w, gders (pending ([], FT t)) w -> gders (pending ([], f)) (s ++ w)) ->
  gders (pending ([], f)) s.
Proof.
  intros f s t H. rewrite <- (app_nil_r s). apply H. constructor.
Qed.

Lemma derives_pending : forall c s c',
  derives c s c' -> forall w, gders (pending c') w -> gders (pending c) (s ++ w).
Proof.
  intros c s c' H; induction H; intros w Hw.
  - exact Hw.
  - (* RW1 *)
    destruct (gders_inv _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (gders_inv _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    simpl. rewrite E, E', app_assoc. constructor; [eapply g_bin; eauto | exact Hr'].
  - (* RW2 *)
    simpl. change (a :: s ++ w) with ([a] ++ (s ++ w)).
    constructor; [apply g_term; assumption | exact (IHderives w Hw)].
  - (* RW3 *)
    pose proof (gders_one _ _ (sub_der _ _ _ IHderives1)) as HB.
    simpl. rewrite <- app_assoc. constructor; [exact HB | exact (IHderives2 w Hw)].
  - (* RW3, slashed *)
    pose proof (gders_one _ _ (sub_der _ _ _ IHderives1)) as HB.
    simpl. rewrite <- app_assoc. constructor; [exact HB | exact (IHderives2 w Hw)].
  - (* RW4 *)
    pose proof (gders_one _ _ (sub_der _ _ _ IHderives1)) as HD.
    destruct (gders_inv _ _ _ (IHderives2 w Hw)) as [u1 [u2 [E [HS Hr]]]].
    simpl. rewrite <- app_assoc, E, app_assoc.
    constructor; [eapply g_top; eauto | exact Hr].
  - (* RW5a *)
    destruct (gders_inv _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (gders_inv _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    simpl. rewrite E, E', app_assoc. constructor; [eapply g_sa; eauto | exact Hr'].
  - (* RW5b *)
    destruct (gders_inv _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (gders_inv _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    simpl. rewrite E, E', app_assoc. constructor; [eapply g_sb; eauto | exact Hr'].
  - (* RW6 *)
    simpl. change (s ++ w) with ([] ++ (s ++ w)).
    constructor; [apply g_gap | exact (IHderives w Hw)].
  - (* RW7 *)
    destruct (gders_inv _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HB Hr]]]].
    destruct (gders_inv _ _ _ Hr) as [v1 [v2 [E' [HL Hr']]]].
    simpl. rewrite E, E', app_assoc. constructor; [eapply g_link; eauto | exact Hr'].
  - (* RW8 *)
    pose proof (gders_one _ _ (sub_der _ _ _ IHderives1)) as HL.
    simpl. rewrite <- app_assoc. constructor; [exact HL | exact (IHderives2 w Hw)].
Qed.

Lemma epg_to_flat : forall S w t,
  derives ([], FNT S) w ([], FT t) -> gder (CN S) w.
Proof.
  intros S w t H. apply gders_one.
  rewrite <- (app_nil_r w). apply (derives_pending _ _ _ H). constructor.
Qed.

(* Weak context-freeness: extended path grammars generate exactly the strings of
   the context-free grammar G-flat; hence their string languages are
   context-free. *)
Theorem epg_weakly_context_free : forall S w,
  epg_language S w <-> flat_language S w.
Proof.
  intros S w; split.
  - intros [t H]. eapply epg_to_flat; eauto.
  - intro H. exact (flat_to_epg _ _ H []).
Qed.

(* ===================================================================== *)
(*  Tree-level characterisation and item completion                      *)
(*  for extended path grammars.                                          *)
(*                                                                       *)
(*  tder (TN A) w t      : A derives w, and t is the term built for it.   *)
(*  tder (TS A D al) w t : A with a D-gap filled by al derives w, and t   *)
(*                         is the term built, with al placed at the gap.  *)
(*  These are derivation trees of G-flat with fillers substituted into    *)
(*  gaps and host copies substituted into LINK gaps.                      *)
(* ===================================================================== *)

Inductive tcat : Type :=
  | TN : nonterminal -> tcat
  | TS : nonterminal -> nonterminal -> term -> tcat.

Inductive tder : tcat -> list terminal -> term -> Prop :=
  | t_term : forall A a,
      In (TRule A a) R -> tder (TN A) [a] (Leaf a)
  | t_bin : forall A B C w1 w2 t1 t2,
      In (PRule A B C) R -> tder (TN C) w1 t1 -> tder (TN B) w2 t2 ->
      tder (TN A) (w1 ++ w2) (Node t1 t2)
  | t_top : forall A D w1 w2 al t,
      In (TopRule A D) R -> tder (TN D) w1 al -> tder (TS A D al) w2 t ->
      tder (TN A) (w1 ++ w2) t
  | t_link : forall A D C B w1 w2 t1 t2,
      In (LRule A D C B) R -> tder (TN B) w1 t1 -> tder (TS C D t1) w2 t2 ->
      tder (TN A) (w1 ++ w2) (Node t1 (LinkT t2))
  | t_sa : forall A B C D al w1 w2 t1 t2,
      In (PRule A B C) R -> tder (TN C) w1 t1 -> tder (TS B D al) w2 t2 ->
      tder (TS A D al) (w1 ++ w2) (Node t1 t2)
  | t_sb : forall A B C D al w1 w2 t1 t2,
      In (PRule A B C) R -> tder (TS C D al) w1 t1 -> tder (TN B) w2 t2 ->
      tder (TS A D al) (w1 ++ w2) (Node t1 t2)
  | t_gap : forall D al, tder (TS D D al) [] al.

Definition tfocus (c : tcat) : focus :=
  match c with
  | TN A => FNT A
  | TS A D al => FSlash A D al
  end.

(* Completeness: every tree-level derivation is realised from any stack. *)
Lemma tder_to_epg : forall c w t,
  tder c w t -> forall X, derives (X, tfocus c) w (X, FT t).
Proof.
  intros c w t H; induction H; intros X; simpl in *.
  - rewrite <- (app_nil_r [a]). eapply d_rw2; [eassumption | apply d_refl].
  - eapply d_rw1; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [apply IHtder2 | apply d_refl].
  - eapply d_rw4; [eassumption | apply IHtder1 | apply IHtder2].
  - eapply d_rw7; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw8; [apply IHtder2 | apply d_refl].
  - eapply d_rw5a; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3s; [apply IHtder2 | apply d_refl].
  - eapply d_rw5b; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [apply IHtder2 | apply d_refl].
  - apply d_rw6. apply d_refl.
Qed.

(* fill t X w T : starting from the term t, attaching trees for the stack
   symbols X (top first) yields T, and these trees have yield w.  A LINK
   site is filled with a linked tree whose gap holds a copy of the term
   accumulated to its left. *)
Inductive fill : term -> list ssym -> list terminal -> term -> Prop :=
  | f_nil : forall t, fill t [] [] t
  | f_nt : forall t B X w1 w2 tB T,
      tder (TN B) w1 tB -> fill (Node t tB) X w2 T ->
      fill t (SNT B :: X) (w1 ++ w2) T
  | f_sl : forall t B D al X w1 w2 tB T,
      tder (TS B D al) w1 tB -> fill (Node t tB) X w2 T ->
      fill t (SSlash B D al :: X) (w1 ++ w2) T
  | f_lk : forall t D C X w1 w2 tL T,
      tder (TS C D t) w1 tL -> fill (Node t (LinkT tL)) X w2 T ->
      fill t (SLink D C :: X) (w1 ++ w2) T.

(* tcontent c w T : item c can be completed, emitting w, to the final term T. *)
Definition tcontent (c : item) (w : list terminal) (T : term) : Prop :=
  match c with
  | (X, FT t) => fill t X w T
  | (X, FNT A) => exists w1 w2 t, w = w1 ++ w2 /\ tder (TN A) w1 t /\ fill t X w2 T
  | (X, FSlash A D al) =>
      exists w1 w2 t, w = w1 ++ w2 /\ tder (TS A D al) w1 t /\ fill t X w2 T
  end.

Lemma sub_tder : forall f s tB,
  (forall w T, tcontent ([], FT tB) w T -> tcontent ([], f) (s ++ w) T) ->
  tcontent ([], f) s tB.
Proof.
  intros f s tB H. rewrite <- (app_nil_r s). apply H. constructor.
Qed.

Lemma tcontent_nil_nt : forall A s tB,
  tcontent ([], FNT A) s tB -> tder (TN A) s tB.
Proof.
  intros A s tB [w1 [w2 [t [E [Ht Hf]]]]].
  inversion Hf; subst. rewrite app_nil_r. exact Ht.
Qed.

Lemma tcontent_nil_sl : forall A D al s tB,
  tcontent ([], FSlash A D al) s tB -> tder (TS A D al) s tB.
Proof.
  intros A D al s tB [w1 [w2 [t [E [Ht Hf]]]]].
  inversion Hf; subst. rewrite app_nil_r. exact Ht.
Qed.

(* Soundness invariant: completion data propagate backwards along a
   derivation, including the nested sub-derivations of RW3, RW4 and RW8. *)
Lemma derives_tcontent : forall c s c',
  derives c s c' -> forall w T, tcontent c' w T -> tcontent c (s ++ w) T.
Proof.
  intros c s c' H; induction H; intros w T Hc.
  - exact Hc.
  - (* RW1 *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_bin; eauto.
    + assumption.
  - (* RW2 *)
    exists [a], (s ++ w), (Leaf a). repeat split.
    + apply t_term; assumption.
    + apply (IHderives w T Hc).
  - (* RW3 *)
    pose proof (tcontent_nil_nt _ _ _ (sub_tder _ _ _ IHderives1)) as HB.
    simpl. rewrite <- app_assoc. eapply f_nt; [exact HB | exact (IHderives2 w T Hc)].
  - (* RW3, slashed *)
    pose proof (tcontent_nil_sl _ _ _ _ _ (sub_tder _ _ _ IHderives1)) as HB.
    simpl. rewrite <- app_assoc. eapply f_sl; [exact HB | exact (IHderives2 w T Hc)].
  - (* RW4 *)
    pose proof (tcontent_nil_nt _ _ _ (sub_tder _ _ _ IHderives1)) as HD.
    destruct (IHderives2 w T Hc) as [w1 [w2 [t [E [Ht Hf]]]]].
    exists (s1 ++ w1), w2, t. repeat split.
    + rewrite <- app_assoc, E. apply app_assoc.
    + eapply t_top; eauto.
    + assumption.
  - (* RW5a *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_sa; eauto.
    + assumption.
  - (* RW5b *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_sb; eauto.
    + assumption.
  - (* RW6 *)
    exists [], (s ++ w), al. repeat split.
    + apply t_gap.
    + apply (IHderives w T Hc).
  - (* RW7 *)
    destruct (IHderives w T Hc) as [w1 [w2 [tB [E [HB Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tB (LinkT tL)). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_link; eauto.
    + assumption.
  - (* RW8 *)
    pose proof (tcontent_nil_sl _ _ _ _ _ (sub_tder _ _ _ IHderives1)) as HL.
    simpl. rewrite <- app_assoc. eapply f_lk; [exact HL | exact (IHderives2 w T Hc)].
Qed.

(* Tree-level characterisation: the terms built by an extended path grammar are exactly the
   tree-level derivations, for plain and for slashed start categories. *)
Theorem epg_tree_characterisation : forall c w t,
  derives ([], tfocus c) w ([], FT t) <-> tder c w t.
Proof.
  intros c w t; split.
  - intro H.
    assert (Hc : tcontent ([], tfocus c) (w ++ []) t)
      by (apply (derives_tcontent _ _ _ H); constructor).
    rewrite app_nil_r in Hc. destruct c; simpl in Hc.
    + apply tcontent_nil_nt. exact Hc.
    + apply tcontent_nil_sl. exact Hc.
  - intro H. exact (tder_to_epg _ _ _ H []).
Qed.

(* Item completion: every item on a derivation that ends in
   the final term T can be completed to T, i.e. T arises from the item's
   partial term by filling its open leaves; pending fillers are placed at
   their gaps and LINK sites receive copies of their hosts. *)
Corollary epg_item_completion : forall c s T,
  derives c s ([], FT T) -> tcontent c s T.
Proof.
  intros c s T H. rewrite <- (app_nil_r s).
  apply (derives_tcontent _ _ _ H). constructor.
Qed.

(* ===================================================================== *)
(*  Flattened derivations and nested item completion.                    *)
(*  Frames record the enclosing step of a nested sub-derivation:        *)
(*    FrP X t     : an RW3 pop of a plain or slashed category;           *)
(*    FrL X t     : an RW8 LINK resolution, host t;                      *)
(*    FrT X A D   : an RW4 fronting step that is building its filler.    *)
(* ===================================================================== *)

Inductive frame : Type :=
  | FrP : list ssym -> term -> frame
  | FrL : list ssym -> term -> frame
  | FrT : list ssym -> nonterminal -> nonterminal -> frame.

Definition config : Type := (list frame * item)%type.

Inductive mstep : config -> list terminal -> config -> Prop :=
  | m_rw1 : forall F X A B C, In (PRule A B C) R ->
      mstep (F, (X, FNT A)) [] (F, (SNT B :: X, FNT C))
  | m_rw2 : forall F X A a, In (TRule A a) R ->
      mstep (F, (X, FNT A)) [a] (F, (X, FT (Leaf a)))
  | m_call3 : forall F X B t,
      mstep (F, (SNT B :: X, FT t)) [] (FrP X t :: F, ([], FNT B))
  | m_call3s : forall F X B D al t,
      mstep (F, (SSlash B D al :: X, FT t)) [] (FrP X t :: F, ([], FSlash B D al))
  | m_ret3 : forall F X t tB,
      mstep (FrP X t :: F, ([], FT tB)) [] (F, (X, FT (Node t tB)))
  | m_call4 : forall F X A D, In (TopRule A D) R ->
      mstep (F, (X, FNT A)) [] (FrT X A D :: F, ([], FNT D))
  | m_ret4 : forall F X A D al,
      mstep (FrT X A D :: F, ([], FT al)) [] (F, (X, FSlash A D al))
  | m_rw5a : forall F X A B C D al, In (PRule A B C) R ->
      mstep (F, (X, FSlash A D al)) [] (F, (SSlash B D al :: X, FNT C))
  | m_rw5b : forall F X A B C D al, In (PRule A B C) R ->
      mstep (F, (X, FSlash A D al)) [] (F, (SNT B :: X, FSlash C D al))
  | m_rw6 : forall F X D al,
      mstep (F, (X, FSlash D D al)) [] (F, (X, FT al))
  | m_rw7 : forall F X A D C B, In (LRule A D C B) R ->
      mstep (F, (X, FNT A)) [] (F, (SLink D C :: X, FNT B))
  | m_call8 : forall F X D C t,
      mstep (F, (SLink D C :: X, FT t)) [] (FrL X t :: F, ([], FSlash C D t))
  | m_ret8 : forall F X t tL,
      mstep (FrL X t :: F, ([], FT tL)) [] (F, (X, FT (Node t (LinkT tL)))).

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
  - eapply ms_one; [apply m_rw1; eassumption | apply IHderives].
  - change (a :: s) with ([a] ++ s). eapply ms_step; [apply m_rw2; eassumption | apply IHderives].
  - eapply ms_one; [apply m_call3 |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret3 | apply IHderives2].
  - eapply ms_one; [apply m_call3s |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret3 | apply IHderives2].
  - eapply ms_one; [apply m_call4; eassumption |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret4 | apply IHderives2].
  - eapply ms_one; [apply m_rw5a; eassumption | apply IHderives].
  - eapply ms_one; [apply m_rw5b; eassumption | apply IHderives].
  - eapply ms_one; [apply m_rw6 | apply IHderives].
  - eapply ms_one; [apply m_rw7; eassumption | apply IHderives].
  - eapply ms_one; [apply m_call8 |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret8 | apply IHderives2].
Qed.

Fixpoint gcontent (F : list frame) (c : item) (w : list terminal) (T : term) : Prop :=
  match F with
  | [] => tcontent c w T
  | FrP X t :: F' => exists w1 w2 tB,
      w = w1 ++ w2 /\ tcontent c w1 tB /\ gcontent F' (X, FT (Node t tB)) w2 T
  | FrL X t :: F' => exists w1 w2 tL,
      w = w1 ++ w2 /\ tcontent c w1 tL /\ gcontent F' (X, FT (Node t (LinkT tL))) w2 T
  | FrT X A D :: F' => exists w1 w2 al,
      w = w1 ++ w2 /\ tcontent c w1 al /\ gcontent F' (X, FSlash A D al) w2 T
  end.

Lemma gcontent_lift : forall c c' s,
  (forall w T, tcontent c' w T -> tcontent c (s ++ w) T) ->
  forall F w T, gcontent F c' w T -> gcontent F c (s ++ w) T.
Proof.
  intros c c' s Hl F w T. destruct F as [| [X t | X t | X A D] F']; simpl.
  - apply Hl.
  - intros [w1 [w2 [tB [E [Hc Hg]]]]]. exists (s ++ w1), w2, tB.
    repeat split; auto. rewrite E. apply app_assoc.
  - intros [w1 [w2 [tB [E [Hc Hg]]]]]. exists (s ++ w1), w2, tB.
    repeat split; auto. rewrite E. apply app_assoc.
  - intros [w1 [w2 [tB [E [Hc Hg]]]]]. exists (s ++ w1), w2, tB.
    repeat split; auto. rewrite E. apply app_assoc.
Qed.

Lemma local_lift : forall c s c',
  derives c s c' -> forall F w T, gcontent F c' w T -> gcontent F c (s ++ w) T.
Proof.
  intros c s c' H. apply gcontent_lift. apply derives_tcontent. exact H.
Qed.

Lemma tcontent_final : forall t, tcontent ([], FT t) [] t.
Proof. intros. constructor. Qed.

Lemma mstep_gcontent : forall k s k',
  mstep k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; inversion H; subst; cbn [fst snd]; intros w T Hg.
  - apply (local_lift _ _ _ (d_rw1 _ _ _ _ _ _ H0 (d_refl _))). exact Hg.
  - apply (local_lift _ _ _ (d_rw2 _ _ _ _ _ H0 (d_refl _))). exact Hg.
  - simpl in Hg. destruct Hg as [w1 [w2 [tB [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' Hc'. simpl. eapply f_nt; [apply tcontent_nil_nt; exact Hc | exact Hc'].
  - simpl in Hg. destruct Hg as [w1 [w2 [tB [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' Hc'. simpl. eapply f_sl; [apply tcontent_nil_sl; exact Hc | exact Hc'].
  - simpl. exists [], w, tB. repeat split; [apply tcontent_final | exact Hg].
  - simpl in Hg. destruct Hg as [w1 [w2 [al [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' [u1 [u2 [t [E' [Ht Hf]]]]].
    exists (w1 ++ u1), u2, t. repeat split.
    + rewrite E'. apply app_assoc.
    + eapply t_top; [eassumption | apply tcontent_nil_nt; exact Hc | exact Ht].
    + exact Hf.
  - simpl. exists [], w, al. repeat split; [apply tcontent_final | exact Hg].
  - eapply local_lift; [eapply d_rw5a; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_rw5b; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_rw6; apply d_refl | exact Hg].
  - eapply local_lift; [eapply d_rw7; [exact H0 | apply d_refl] | exact Hg].
  - simpl in Hg. destruct Hg as [w1 [w2 [tL [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' Hc'. simpl. eapply f_lk; [apply tcontent_nil_sl; exact Hc | exact Hc'].
  - simpl. exists [], w, tL. repeat split; [apply tcontent_final | exact Hg].
Qed.

Lemma msteps_gcontent : forall k s k',
  msteps k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; induction H; intros w T Hg.
  - exact Hg.
  - rewrite <- app_assoc. eapply mstep_gcontent; [exact H | apply IHmsteps; exact Hg].
Qed.

(* Nested item completion for extended derivations (Corollary 8),
   including items inside the sub-derivations of RW3, RW4 and RW8. *)
Corollary epg_nested_item_completion : forall k s T,
  msteps k s ([], ([], FT T)) -> gcontent (fst k) (snd k) s T.
Proof.
  intros k s T H. rewrite <- (app_nil_r s).
  apply (msteps_gcontent _ _ _ H). simpl. constructor.
Qed.

Theorem epg_machine_equivalence : forall c w t,
  msteps ([], ([], tfocus c)) w ([], ([], FT t)) <-> derives ([], tfocus c) w ([], FT t).
Proof.
  intros c w t; split.
  - intro H. apply epg_tree_characterisation.
    pose proof (epg_nested_item_completion _ _ _ H) as Hg. simpl in Hg.
    destruct c; simpl in Hg; [apply tcontent_nil_nt | apply tcontent_nil_sl]; exact Hg.
  - intro H. exact (derives_to_machine _ _ _ H []).
Qed.

(* ===================================================================== *)
(*  Each filler occupies exactly one gap: the term built for a slashed   *)
(*  category is a one-hole context, independent of the filler, applied   *)
(*  to the filler.                                                       *)
(* ===================================================================== *)

Inductive ctx : Type :=
  | Hole : ctx
  | CL : ctx -> term -> ctx
  | CR : term -> ctx -> ctx.

Fixpoint plug (k : ctx) (al : term) : term :=
  match k with
  | Hole => al
  | CL k' r => Node (plug k' al) r
  | CR l k' => Node l (plug k' al)
  end.

Lemma unique_gap_gen : forall c w t, tder c w t ->
  match c with
  | TS A D al => exists k, t = plug k al /\ forall al', tder (TS A D al') w (plug k al')
  | TN _ => True
  end.
Proof.
  intros c w t H; induction H; auto.
  - destruct IHtder2 as [k [E Hk]]. exists (CR t1 k). split.
    + simpl. rewrite E. reflexivity.
    + intro al'. simpl. eapply t_sa; eauto.
  - destruct IHtder1 as [k [E Hk]]. exists (CL k t2). split.
    + simpl. rewrite E. reflexivity.
    + intro al'. simpl. eapply t_sb; eauto.
  - exists Hole. split; [reflexivity | intro al'; apply t_gap].
Qed.

Corollary unique_gap : forall A D al w t,
  tder (TS A D al) w t ->
  exists k, t = plug k al /\ forall al', tder (TS A D al') w (plug k al').
Proof. intros. exact (unique_gap_gen _ _ _ H). Qed.

(* ===================================================================== *)
(*  Extended path grammars are epsilon-free (Corollary 6), and on rules   *)
(*  of the basic forms they build exactly the derivation trees of the     *)
(*  underlying CFG (so they generate every epsilon-free CFL).             *)
(* ===================================================================== *)

Lemma gder_nonempty_gen : forall c w, gder c w ->
  match c with CN _ => w <> [] | CS _ _ => True end.
Proof.
  intros c w H; induction H; auto; try (intro E; apply app_eq_nil in E; destruct E; contradiction).
  discriminate.
Qed.

Corollary epg_epsilon_free : forall S w, epg_language S w -> w <> [].
Proof.
  intros S w Hw. apply epg_weakly_context_free in Hw. exact (gder_nonempty_gen _ _ Hw).
Qed.

Inductive bder : nonterminal -> list terminal -> term -> Prop :=
  | b_term : forall A a, In (TRule A a) R -> bder A [a] (Leaf a)
  | b_bin : forall A B C w1 w2 t1 t2, In (PRule A B C) R ->
      bder C w1 t1 -> bder B w2 t2 -> bder A (w1 ++ w2) (Node t1 t2).

Definition basic_rules : Prop :=
  forall r, In r R -> match r with PRule _ _ _ | TRule _ _ => True | _ => False end.

Lemma basic_fragment_gen : basic_rules -> forall c w t, tder c w t ->
  match c with TN A => bder A w t | TS _ _ _ => True end.
Proof.
  intros HR c w t H; induction H; auto.
  - apply b_term; assumption.
  - eapply b_bin; eauto.
  - exfalso. exact (HR _ H).
  - exfalso. exact (HR _ H).
Qed.

Theorem basic_fragment : basic_rules -> forall A w t,
  derives ([], FNT A) w ([], FT t) <-> bder A w t.
Proof.
  intros HR A w t. rewrite (epg_tree_characterisation (TN A)). split.
  - intro H. exact (basic_fragment_gen HR _ _ _ H).
  - intro H. induction H; [apply t_term | eapply t_bin]; eauto.
Qed.

End Extended.

(* ===================================================================== *)
(*  The binding example: for "Himself, John likes" the only term built   *)
(*  is (John, (likes, himself)), with the reflexive in object position.  *)
(* ===================================================================== *)

Section Binding.

Inductive bnt : Type := bS | bVP | bNP | bV.
Inductive btm : Type := John | likes | himself.

Definition RB : list (rule btm bnt) :=
  [PRule _ _ bS bVP bNP; PRule _ _ bVP bNP bV; TRule _ _ bV likes;
   TRule _ _ bNP John; TRule _ _ bNP himself; TopRule _ _ bS bNP].

Notation td := (tder btm bnt RB).
Notation TNb := (TN btm bnt).
Notation TSb := (TS btm bnt).
Notation Lf := (Leaf btm).
Notation Nd := (Node btm).

Ltac rb := match goal with H : In _ RB |- _ =>
  simpl in H;
  repeat (destruct H as [H|H]; [try discriminate H; inversion H; subst; clear H |]);
  try contradiction end.

Lemma np_char : forall w t, td (TNb bNP) w t ->
  (w = [John] /\ t = Lf John) \/ (w = [himself] /\ t = Lf himself).
Proof. intros w t H; inversion H; subst; rb; auto. Qed.

Lemma v_char : forall w t, td (TNb bV) w t -> w = [likes] /\ t = Lf likes.
Proof. intros w t H; inversion H; subst; rb; auto. Qed.

Lemma vp_char : forall w t, td (TNb bVP) w t ->
  exists x tx, td (TNb bNP) x tx /\ w = likes :: x /\ t = Nd (Lf likes) tx.
Proof.
  intros w t H; inversion H; subst; rb.
  match goal with h : td (TNb bV) _ _ |- _ => apply v_char in h; destruct h; subst end.
  eauto.
Qed.

Lemma npnp_char : forall al w t, td (TSb bNP bNP al) w t -> w = [] /\ t = al.
Proof. intros al w t H; inversion H; subst; try rb; try discriminate; auto. Qed.

Lemma vnp_char : forall al w t, td (TSb bV bNP al) w t -> False.
Proof. intros al w t H; inversion H; subst; try rb; try discriminate. Qed.

Lemma vpnp_char : forall al w t, td (TSb bVP bNP al) w t ->
  w = [likes] /\ t = Nd (Lf likes) al.
Proof.
  intros al w t H; inversion H; subst; try rb; try discriminate.
  - match goal with h : td (TNb bV) _ _ |- _ => apply v_char in h; destruct h; subst end.
    match goal with h : td (TSb bNP bNP _) _ _ |- _ => apply npnp_char in h; destruct h; subst end.
    auto.
  - exfalso. match goal with h : td (TSb bV bNP _) _ _ |- _ => exact (vnp_char _ _ _ h) end.
Qed.

Lemma snp_char : forall al w t, td (TSb bS bNP al) w t ->
  (exists x tx, td (TNb bNP) x tx /\ w = x ++ [likes] /\ t = Nd tx (Nd (Lf likes) al)) \/
  (exists x tx, td (TNb bNP) x tx /\ w = likes :: x /\ t = Nd al (Nd (Lf likes) tx)).
Proof.
  intros al w t H; inversion H; subst; try rb; try discriminate.
  - left. match goal with h : td (TSb bVP bNP _) _ _ |- _ => apply vpnp_char in h; destruct h; subst end.
    eauto.
  - right. match goal with h : td (TSb bNP bNP _) _ _ |- _ => apply npnp_char in h; destruct h; subst end.
    match goal with h : td (TNb bVP) _ _ |- _ =>
      apply vp_char in h; destruct h as [x [tx [Hx [E E']]]]; subst end.
    eauto.
Qed.

Theorem binding_example : forall t,
  derives btm bnt RB ([], FNT btm bnt bS) [himself; John; likes] ([], FT btm bnt t) <->
  t = Nd (Lf John) (Nd (Lf likes) (Lf himself)).
Proof.
  intro t. rewrite (epg_tree_characterisation btm bnt RB (TNb bS)). split.
  - intro H. inversion H; subst; rb.
    + (* S -> [VP] NP without fronting: the VP would have to start with "likes" *)
      match goal with h : td (TNb bVP) _ _ |- _ =>
        apply vp_char in h; destruct h as [x [tx [Hx [E E']]]]; subst end.
      match goal with h : td (TNb bNP) ?w _, e : ?w ++ _ = _ |- _ =>
        apply np_char in h; destruct h as [[E1 E2] | [E1 E2]]; subst; simpl in e; inversion e end.
    + (* fronting *)
      match goal with h : td (TNb bNP) ?w _, e : ?w ++ _ = _ |- _ =>
        apply np_char in h; destruct h as [[E1 E2] | [E1 E2]]; subst; simpl in e; inversion e; subst end.
      match goal with h : td (TSb bS bNP _) _ _ |- _ =>
        apply snp_char in h; destruct h as [[x [tx [Hx [E E']]]] | [x [tx [Hx [E E']]]]]; subst end.
      * apply np_char in Hx. destruct Hx as [[-> ->] | [-> ->]]; [reflexivity | discriminate E].
      * discriminate E.
  - intros ->.
    change [himself; John; likes] with ([himself] ++ ([John] ++ ([likes] ++ []))).
    eapply t_top; [simpl; tauto | apply t_term; simpl; tauto |].
    eapply t_sa; [simpl; tauto | apply t_term; simpl; tauto |].
    eapply t_sa; [simpl; tauto | apply t_term; simpl; tauto | apply t_gap].
Qed.

End Binding.
