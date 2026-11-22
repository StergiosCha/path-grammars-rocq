(* ===================================================================== *)
(*  Cross-serial dependencies (Proposition 13): the indexed path grammar *)
(*  P_x of Example 5 generates exactly { a^n b^m c^n d^m | n, m >= 1 }.   *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc IndexedPathGrammars.v CrossSerial.v).    *)
(* ===================================================================== *)

Require Import List Lia Arith.
Import ListNotations.
Require Import IndexedPathGrammars.

Inductive nt : Type :=
  | N_S | N_S1 | N_S2 | N_U | N_U1 | N_U2 | N_V | N_V1 | N_W | N_W1
  | N_A | N_B | N_C | N_D.
Inductive ix : Type := iI | iJ.
Inductive tm : Type := ta | tb | tc | td.

(* Index stacks are lists with the top at the head, so the paper's
   stack i^n j^m (top j) is  rep iJ m ++ rep iI n. *)
Definition RX : list (irule tm nt ix) :=
  [ IBinD _ _ _ N_S N_S1 N_A;            (* S[..]  -> [S1[..]] A[]      *)
    IPush _ _ _ N_S1 iI N_S2;            (* S1[..] -> S2[..i]           *)
    IChain _ _ _ N_S2 N_S;               (* S2[..] -> S[..]             *)
    IChain _ _ _ N_S2 N_U;               (* S2[..] -> U[..]             *)
    IBinD _ _ _ N_U N_U1 N_B;            (* U[..]  -> [U1[..]] B[]      *)
    IPush _ _ _ N_U1 iJ N_U2;            (* U1[..] -> U2[..j]           *)
    IChain _ _ _ N_U2 N_U;               (* U2[..] -> U[..]             *)
    IChain _ _ _ N_U2 N_V;               (* U2[..] -> V[..]             *)
    IPop _ _ _ N_V iJ N_V1;              (* V[..j] -> V1[..]            *)
    IBinP _ _ _ N_V1 N_D N_V;            (* V1[..] -> [D[]] V[..]       *)
    IBinP _ _ _ N_V1 N_D N_W;            (* V1[..] -> [D[]] W[..]       *)
    IPop _ _ _ N_W iI N_W1;              (* W[..i] -> W1[..]            *)
    IBinP _ _ _ N_W1 N_C N_W;            (* W1[..] -> [C[]] W[..]       *)
    ITerm _ _ _ N_W1 (Some tc);          (* W1[]   -> c                 *)
    ITerm _ _ _ N_A (Some ta);
    ITerm _ _ _ N_B (Some tb);
    ITerm _ _ _ N_C (Some tc);
    ITerm _ _ _ N_D (Some td) ].

Notation ld := (lig_der tm nt ix RX).

Fixpoint rep {X : Type} (x : X) (n : nat) : list X :=
  match n with 0 => [] | S n' => x :: rep x n' end.

Lemma rep_add : forall {X} (x : X) n m, rep x n ++ rep x m = rep x (n + m).
Proof. intros X x n m. induction n; simpl; congruence. Qed.

Lemma rep_snoc : forall {X} (x : X) n, rep x n ++ [x] = rep x (S n).
Proof.
  intros X x n. change [x] with (rep x 1). rewrite rep_add. f_equal. lia.
Qed.

(* ---------------- The language of each indexed non-terminal ------- *)

Definition spec (c : nt * list ix) (w : list tm) : Prop :=
  match c with
  | (N_A, s) => s = [] /\ w = [ta]
  | (N_B, s) => s = [] /\ w = [tb]
  | (N_C, s) => s = [] /\ w = [tc]
  | (N_D, s) => s = [] /\ w = [td]
  | (N_W, s) => exists k, s = rep iI (S k) /\ w = rep tc (S k)
  | (N_W1, s) => exists k, s = rep iI k /\ w = rep tc (S k)
  | (N_V, s) => exists n m, s = rep iJ (S m) ++ rep iI (S n) /\
                            w = rep tc (S n) ++ rep td (S m)
  | (N_V1, s) => exists n m, s = rep iJ m ++ rep iI (S n) /\
                             w = rep tc (S n) ++ rep td (S m)
  | (N_U, s) => exists n k m, s = rep iJ k ++ rep iI (S n) /\
                              w = rep tb (S m) ++ rep tc (S n) ++ rep td (S m + k)
  | (N_U1, s) => exists n k m, s = rep iJ k ++ rep iI (S n) /\
                               w = rep tb m ++ rep tc (S n) ++ rep td (S (m + k))
  | (N_U2, s) => exists n k m, s = rep iJ k ++ rep iI (S n) /\ 1 <= m + k /\
                               w = rep tb m ++ rep tc (S n) ++ rep td (m + k)
  | (N_S, s) => exists k p m, s = rep iI k /\
                              w = rep ta (S p) ++ rep tb (S m) ++ rep tc (S p + k) ++ rep td (S m)
  | (N_S1, s) => exists k p m, s = rep iI k /\
                               w = rep ta p ++ rep tb (S m) ++ rep tc (S (p + k)) ++ rep td (S m)
  | (N_S2, s) => (exists k p m, s = rep iI k /\
                    w = rep ta (S p) ++ rep tb (S m) ++ rep tc (S p + k) ++ rep td (S m)) \/
                  (exists n k m, s = rep iJ k ++ rep iI (S n) /\
                    w = rep tb (S m) ++ rep tc (S n) ++ rep td (S m + k))
  end.

Ltac inRX H := simpl in H;
  repeat (destruct H as [H|H]; [try discriminate H; inversion H; subst; clear H |]);
  try contradiction.

Lemma rep_length : forall {X} (x : X) n, length (rep x n) = n.
Proof. intros X x n. induction n; simpl; congruence. Qed.

Lemma rep_JI_I : forall k n k', rep iJ k ++ rep iI (S n) = rep iI k' -> k = 0 /\ k' = S n.
Proof.
  intros k n k' E. destruct k; simpl in E.
  - split; [reflexivity |]. apply (f_equal (@length ix)) in E.
    simpl in E. rewrite !rep_length in E. lia.
  - destruct k'; discriminate E.
Qed.

Ltac sp := cbv beta iota delta [spec] in *.

Lemma soundness : forall c w t, ld c w t -> spec c w.
Proof.
  intros c w t H; induction H.
  - (* IBinP *) inRX H; sp.
    + (* V1 -> [D] V *)
      destruct IHlig_der1 as [n [m [Es Ew]]]. destruct IHlig_der2 as [_ Ew2]. subst.
      exists n, (S m). split; [reflexivity |].
      rewrite <- app_assoc, rep_snoc. reflexivity.
    + (* V1 -> [D] W *)
      destruct IHlig_der1 as [k [Es Ew]]. destruct IHlig_der2 as [_ Ew2]. subst.
      exists k, 0. split; reflexivity.
    + (* W1 -> [C] W *)
      destruct IHlig_der1 as [k [Es Ew]]. destruct IHlig_der2 as [_ Ew2]. subst.
      exists (S k). split; [reflexivity | apply rep_snoc].
  - (* IBinD *) inRX H; sp.
    + (* S -> [S1] A *)
      destruct IHlig_der1 as [_ Ew1]. destruct IHlig_der2 as [k [p [m [Es Ew]]]]. subst.
      exists k, p, m. split; reflexivity.
    + (* U -> [U1] B *)
      destruct IHlig_der1 as [_ Ew1]. destruct IHlig_der2 as [n [k [m [Es Ew]]]]. subst.
      exists n, k, m. split; reflexivity.
  - (* IPush *) inRX H; sp.
    + (* S1 -> S2[..i] *)
      destruct IHlig_der as [[k [p [m [Es Ew]]]] | [n [k [m [Es Ew]]]]].
      * destruct k as [|k]; [discriminate Es |]. simpl in Es. inversion Es; subst.
        exists k, (S p), m. split; [reflexivity |].
        replace (S (S p + k)) with (S p + S k) by lia. reflexivity.
      * destruct k as [|k]; [| discriminate Es]. simpl in Es. inversion Es; subst.
        exists n, 0, m. split; [reflexivity |].
        replace (S m + 0) with (S m) by lia. reflexivity.
    + (* U1 -> U2[..j] *)
      destruct IHlig_der as [n [k [m [Es [Hk Ew]]]]].
      destruct k as [|k]; simpl in Es; [discriminate Es |]. inversion Es; subst.
      exists n, k, m. split; [reflexivity |].
      replace (S (m + k)) with (m + S k) by lia. reflexivity.
  - (* IPop *) inRX H; sp.
    + (* V[..j] -> V1 *)
      destruct IHlig_der as [n [m [Es Ew]]]. subst. exists n, m. split; reflexivity.
    + (* W[..i] -> W1 *)
      destruct IHlig_der as [k [Es Ew]]. subst. exists k. split; reflexivity.
  - (* IChain *) inRX H; sp.
    + (* S2 -> S *) left. exact IHlig_der.
    + (* S2 -> U *) right. exact IHlig_der.
    + (* U2 -> U *)
      destruct IHlig_der as [n [k [m [Es Ew]]]]. subst.
      exists n, k, (S m). split; [reflexivity | split; [lia | reflexivity]].
    + (* U2 -> V *)
      destruct IHlig_der as [n [m [Es Ew]]]. subst.
      exists n, (S m), 0. split; [reflexivity | split; [lia | reflexivity]].
  - (* ITerm *) inRX H; sp; try (exists 0); split; reflexivity.
Qed.

(* ---------------- Completeness ---------------------------------------- *)

Lemma ld_rule : forall r, In r RX -> In r RX.
Proof. auto. Qed.

Ltac rule := simpl; tauto.

Lemma W_complete : forall k,
  (exists t, ld (N_W, rep iI (S k)) (rep tc (S k)) t) /\
  (exists t, ld (N_W1, rep iI k) (rep tc (S k)) t).
Proof.
  induction k.
  - assert (H1 : exists t, ld (N_W1, []) [tc] t)
      by (eexists; change [tc] with (emit tm (Some tc)); apply l_term; rule).
    split; [| exact H1].
    destruct H1 as [t H1]. eexists. simpl. eapply l_pop; [rule | exact H1].
  - destruct IHk as [[t1 H1] _].
    assert (H2 : exists t, ld (N_W1, rep iI (S k)) (rep tc (S (S k))) t).
    { eexists. replace (rep tc (S (S k))) with (rep tc (S k) ++ [tc]) by apply rep_snoc.
      eapply l_binp; [rule | exact H1 |].
      change [tc] with (emit tm (Some tc)). apply l_term; rule. }
    split; [| exact H2].
    destruct H2 as [t2 H2]. eexists. simpl. eapply l_pop; [rule | exact H2].
Qed.

Lemma V_complete : forall n m,
  exists t, ld (N_V, rep iJ (S m) ++ rep iI (S n)) (rep tc (S n) ++ rep td (S m)) t.
Proof.
  intros n m. induction m.
  - destruct (W_complete n) as [[t1 H1] _].
    eexists. simpl. eapply l_pop; [rule |].
    change (tc :: rep tc n ++ [td]) with (rep tc (S n) ++ emit tm (Some td)).
    eapply (l_binp tm nt ix RX N_V1 N_D N_W); [rule | exact H1 | apply l_term; rule].
  - destruct IHm as [t1 H1].
    eexists. change (rep iJ (S (S m)) ++ rep iI (S n)) with (iJ :: (rep iJ (S m) ++ rep iI (S n))).
    eapply l_pop; [rule |].
    replace (rep tc (S n) ++ rep td (S (S m))) with ((rep tc (S n) ++ rep td (S m)) ++ [td])
      by (rewrite <- app_assoc, rep_snoc; reflexivity).
    change [td] with (emit tm (Some td)).
    eapply (l_binp tm nt ix RX N_V1 N_D N_V); [rule | exact H1 | apply l_term; rule].
Qed.

Lemma U_complete : forall m k n,
  exists t, ld (N_U, rep iJ k ++ rep iI (S n))
               (rep tb (S m) ++ rep tc (S n) ++ rep td (S m + k)) t.
Proof.
  induction m; intros k n.
  - destruct (V_complete n k) as [t1 H1].
    eexists. change (rep tb 1 ++ rep tc (S n) ++ rep td (1 + k))
      with (emit tm (Some tb) ++ (rep tc (S n) ++ rep td (S k))).
    eapply l_bind; [rule | apply l_term; rule |].
    eapply l_push; [rule |]. eapply (l_chain tm nt ix RX N_U2 N_V); [rule | exact H1].
  - destruct (IHm (S k) n) as [t1 H1].
    eexists. change (rep tb (S (S m))) with (emit tm (Some tb) ++ rep tb (S m)).
    rewrite <- app_assoc.
    replace (S (S m) + k) with (S m + S k) by lia.
    eapply l_bind; [rule | apply l_term; rule |].
    eapply l_push; [rule |]. eapply (l_chain tm nt ix RX N_U2 N_U); [rule | exact H1].
Qed.

Lemma S_complete : forall p k m,
  exists t, ld (N_S, rep iI k)
               (rep ta (S p) ++ rep tb (S m) ++ rep tc (S p + k) ++ rep td (S m)) t.
Proof.
  induction p; intros k m.
  - destruct (U_complete m 0 k) as [t1 H1]. rewrite Nat.add_0_r in H1.
    eexists. change (rep ta 1) with (emit tm (Some ta)).
    eapply l_bind; [rule | apply l_term; rule |].
    eapply l_push; [rule |]. eapply (l_chain tm nt ix RX N_S2 N_U); [rule |].
    simpl in H1 |- *. exact H1.
  - destruct (IHp (S k) m) as [t1 H1].
    eexists. change (rep ta (S (S p))) with (emit tm (Some ta) ++ rep ta (S p)).
    rewrite <- app_assoc.
    replace (S (S p) + k) with (S p + S k) by lia.
    eapply l_bind; [rule | apply l_term; rule |].
    eapply l_push; [rule |]. eapply (l_chain tm nt ix RX N_S2 N_S); [rule | exact H1].
Qed.

(* Proposition 13 (language part). *)
Theorem cross_serial_lig : forall w,
  (exists t, ld (N_S, []) w t) <->
  exists n m, w = rep ta (S n) ++ rep tb (S m) ++ rep tc (S n) ++ rep td (S m).
Proof.
  intro w; split.
  - intros [t H]. apply soundness in H. simpl in H.
    destruct H as [k [p [m [Es Ew]]]]. destruct k; [| discriminate Es].
    subst. exists p, m. rewrite Nat.add_0_r. reflexivity.
  - intros [n [m ->]]. destruct (S_complete n 0 m) as [t H].
    rewrite Nat.add_0_r in H. eauto.
Qed.

Theorem cross_serial_language : forall w,
  ipg_language tm nt ix RX N_S w <->
  exists n m, w = rep ta (S n) ++ rep tb (S m) ++ rep tc (S n) ++ rep td (S m).
Proof.
  intro w. rewrite <- cross_serial_lig. unfold ipg_language.
  split; intros [t H]; exists t; apply ipg_lig_equivalence; exact H.
Qed.
