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

(* Theorem 3: extended path grammars generate exactly the strings of
   the context-free grammar G-flat; hence their string languages are
   context-free. *)
Theorem epg_weakly_context_free : forall S w,
  epg_language S w <-> flat_language S w.
Proof.
  intros S w; split.
  - intros [t H]. eapply epg_to_flat; eauto.
  - intro H. exact (flat_to_epg _ _ H []).
Qed.

End Extended.
