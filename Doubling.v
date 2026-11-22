(* ===================================================================== *)
(*  Host copying and exponential divergence (Corollary 9):               *)
(*  a four-rule extended path grammar accepts a r^n, and the term built  *)
(*  for a r^n has an expanded yield with exactly 2^n occurrences of a.   *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc ExtendedPathGrammars.v Doubling.v).      *)
(* ===================================================================== *)

Require Import List Lia Arith.
Import ListNotations.
Require Import ExtendedPathGrammars.

Inductive dn : Type := dS | dR | dR'.
Inductive dt : Type := ta | tr.

Definition RD : list (rule dt dn) :=
  [TRule _ _ dS ta; LRule _ _ dS dS dR dS; PRule _ _ dR dS dR'; TRule _ _ dR' tr].

Notation td := (tder dt dn RD).

Fixpoint ey (t : term dt) : list dt :=
  match t with Leaf _ x => [x] | Node _ l r => ey l ++ ey r | LinkT _ u => ey u end.

Fixpoint rep {X} (x : X) n : list X := match n with 0 => [] | S k => x :: rep x k end.
Definition na (w : list dt) := length (filter (fun x => match x with ta => true | tr => false end) w).

Lemma na_app : forall u v, na (u ++ v) = na u + na v.
Proof. intros. unfold na. rewrite filter_app, app_length. reflexivity. Qed.

Lemma na_tr : forall x, na (tr :: x) = na x.
Proof. reflexivity. Qed.

Lemma rep_snoc : forall {X} (x : X) n, rep x n ++ [x] = rep x (S n).
Proof. intros X x n; induction n; simpl in *; [reflexivity | rewrite IHn; reflexivity]. Qed.

Ltac rb := match goal with H : In _ RD |- _ =>
  simpl in H; repeat (destruct H as [H|H]; [try discriminate H; inversion H; subst; clear H |]);
  try contradiction end.

Definition spec (c : tcat dt dn) (w : list dt) (t : term dt) : Prop :=
  match c with
  | TN _ _ dS => exists n, w = ta :: rep tr n /\ na (ey t) = 2 ^ n
  | TN _ _ dR' => w = [tr] /\ t = Leaf _ tr
  | TS _ _ dR dS al => w = [tr] /\ t = Node _ (Leaf _ tr) al
  | TS _ _ dS dS al => w = [] /\ t = al
  | TS _ _ dR' D al => D = dR' /\ w = [] /\ t = al
  | _ => True
  end.

Lemma sound : forall c w t, td c w t -> spec c w t.
Proof.
  intros c w t H; induction H; try rb; try discriminate; simpl in *; auto.
  - exists 0. auto.
  - (* LINK: S -> [LINK_S(R)] S *)
    destruct IHtder1 as [n [Ew Ea]]. destruct IHtder2 as [Ew2 Et]. subst.
    exists (S n). split.
    + simpl. f_equal. exact (rep_snoc tr n).
    + simpl ey. rewrite na_app, na_tr, Ea. simpl. lia.
  - (* R/S -> [S/S] R' *)
    destruct D; simpl in *; auto. destruct IHtder1 as [-> ->]. destruct IHtder2 as [-> ->]. auto.
  - destruct D; simpl in *; auto. destruct IHtder1 as [E _]. discriminate E.
  - destruct D; simpl; auto.
Qed.

Theorem doubling : forall w t, td (TN _ _ dS) w t ->
  exists n, w = ta :: rep tr n /\ na (ey t) = 2 ^ n.
Proof. intros. exact (sound _ _ _ H). Qed.

Lemma w_succ : forall n, ta :: rep tr (S n) = (ta :: rep tr n) ++ ([tr] ++ []).
Proof. intro n. simpl. rewrite rep_snoc. reflexivity. Qed.

Lemma complete : forall n, exists t, td (TN _ _ dS) (ta :: rep tr n) t.
Proof.
  induction n.
  - eexists. change [ta] with (@app dt [ta] []). apply t_term. simpl; tauto.
  - destruct IHn as [t Ht]. eexists.
    rewrite w_succ.
    eapply t_link; [simpl; tauto | exact Ht |].
    eapply t_sa; [simpl; tauto | apply t_term; simpl; tauto | apply t_gap].
Qed.

(* The corollary in terms of the rewrite semantics: the language is a r*,
   and the term built for a r^n has 2^n occurrences of a in its expanded
   yield (linked trees are expanded, ey (LinkT t) = ey t). *)
Theorem doubling_language : forall w,
  epg_language dt dn RD dS w <-> exists n, w = ta :: rep tr n.
Proof.
  intro w; split.
  - intros [t H]. apply (epg_tree_characterisation dt dn RD (TN _ _ dS)) in H.
    destruct (doubling _ _ H) as [n [E _]]. eauto.
  - intros [n ->]. destruct (complete n) as [t H]. exists t.
    apply (epg_tree_characterisation dt dn RD (TN _ _ dS)). exact H.
Qed.

Theorem doubling_terms : forall n t,
  derives dt dn RD ([], FNT dt dn dS) (ta :: rep tr n) ([], FT dt dn t) ->
  na (ey t) = 2 ^ n.
Proof.
  intros n t H. apply (epg_tree_characterisation dt dn RD (TN _ _ dS)) in H.
  destruct (doubling _ _ H) as [m [E Ea]].
  assert (m = n) as ->.
  { injection E as E. apply (f_equal (@length dt)) in E.
    clear -E. revert n E. induction m; intros [|n] E; simpl in E; try discriminate; auto. }
  exact Ea.
Qed.

(* ===================================================================== *)
(*  The exact term and the projected yield lengths (contributed by       *)
(*  Stergios Chatzikyriakidis): each input a r^n has exactly one term,    *)
(*  output n, and erasing r from the expanded yields gives exactly the    *)
(*  lengths 2^n, which are not ultimately periodic.                      *)
(* ===================================================================== *)

Fixpoint output (n : nat) : term dt :=
  match n with
  | 0 => Leaf dt ta
  | S k => let t := output k in Node dt t (LinkT dt (Node dt (Leaf dt tr) t))
  end.

Definition accepted w t :=
  derives dt dn RD ([], FNT dt dn dS) w ([], FT dt dn t).

Lemma canonical : forall w t, td (TN dt dn dS) w t ->
  exists n, w = ta :: rep tr n /\ t = output n.
Proof.
  intros w t H. remember (TN dt dn dS) as c eqn:E.
  induction H; inversion E; subst; try rb.
  - exists 0. auto.
  - destruct (IHtder1 eq_refl) as [n [-> ->]].
    match goal with Hs : td (TS _ _ dR dS _) _ _ |- _ =>
      destruct (sound _ _ _ Hs) as [-> ->] end.
    exists (S n). split; [symmetry; apply w_succ | reflexivity].
Qed.

Lemma rep_len : forall {X} (x : X) n, length (rep x n) = n.
Proof. intros X x n. induction n; simpl; auto. Qed.

Theorem unique_output : forall n t,
  accepted (ta :: rep tr n) t <-> t = output n.
Proof.
  intros n t.
  assert (identify : forall u, accepted (ta :: rep tr n) u -> u = output n).
  { intros u H. apply (epg_tree_characterisation dt dn RD (TN dt dn dS)) in H.
    destruct (canonical _ _ H) as [k [Hw ->]].
    apply (f_equal (@length dt)) in Hw. simpl in Hw.
    rewrite !rep_len in Hw. f_equal; lia. }
  split; [apply identify | intros ->].
  destruct (complete n) as [u Hu].
  apply (epg_tree_characterisation dt dn RD (TN dt dn dS)) in Hu.
  rewrite <- (identify u Hu). exact Hu.
Qed.

Definition projected_count m := exists w t, accepted w t /\ na (ey t) = m.

Theorem exact_projection : forall m, projected_count m <-> exists n, m = 2^n.
Proof.
  intro m. split.
  - intros [w [t [Hw <-]]].
    apply (epg_tree_characterisation dt dn RD (TN dt dn dS)) in Hw.
    destruct (doubling _ _ Hw) as [n [_ H]]. eauto.
  - intros [n ->]. destruct (complete n) as [t H].
    apply (epg_tree_characterisation dt dn RD (TN dt dn dS)) in H.
    exists (ta :: rep tr n), t. split; [exact H | exact (doubling_terms n t H)].
Qed.
Theorem not_ultimately_periodic :
  ~ exists N p, 0 < p /\ forall m, N <= m ->
    (projected_count m <-> projected_count (m + p)).
Proof.
  intros [N [p [Hp Hper]]]. set (k := N+p).
  assert (Hbig : k < 2^k) by (apply Nat.pow_gt_lin_r; lia).
  assert (Hcut : N <= 2^k) by (unfold k in *; lia).
  assert (Hstep : p < 2^k) by (unfold k in *; lia).
  assert (Hpow : projected_count (2^k)) by (apply exact_projection; eauto).
  apply (proj1 (Hper _ Hcut)) in Hpow.
  apply exact_projection in Hpow. destruct Hpow as [j Hj].
  destruct (le_dec j k).
  - pose proof (Nat.pow_le_mono_r 2 j k ltac:(lia) l). lia.
  - assert (Hle : S k <= j) by lia.
    pose proof (Nat.pow_le_mono_r 2 (S k) j ltac:(lia) Hle).
    rewrite Nat.pow_succ_r' in H. lia.
Qed.
