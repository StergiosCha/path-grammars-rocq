(* ===================================================================== *)
(*  The LIG normal form (Lemma 9): every linear indexed grammar has a    *)
(*  normal-form LIG with the same language, and hence (by the IPG/LIG    *)
(*  correspondence) an indexed path grammar with the same language.      *)
(*                                                                       *)
(*  Checked with Coq 8.18 (coqc IndexedPathGrammars.v LIGNormalForm.v).  *)
(* ===================================================================== *)

Require Import List Lia Arith.
Import ListNotations.
Require Import IndexedPathGrammars.

Section NormalForm.

Variables T N I : Type.

(* ---------------------------------------------------------------- *)
(* General LIG productions.  Index stacks are lists with the top at  *)
(* the head.                                                         *)
(*   GProd A eta Ls B eta' Rs :                                      *)
(*     A[.. eta] -> Ls[] B[.. eta'] Rs[]                             *)
(*   (eta and eta' listed top first; Ls and Rs are the non-           *)
(*   distinguished sisters to the left and right of B)               *)
(*   GTerm A o : A[] -> a  or  A[] -> eps                             *)
(* ---------------------------------------------------------------- *)
Inductive gprod : Type :=
  | GProd : N -> list I -> list N -> N -> list I -> list N -> gprod
  | GTerm : N -> option T -> gprod.

Variable G : list gprod.

Inductive gder : (N * list I) -> list T -> Prop :=
  | gd_prod : forall A eta Ls B eta' Rs iota wl wb wr,
      In (GProd A eta Ls B eta' Rs) G ->
      gders Ls wl -> gder (B, eta' ++ iota) wb -> gders Rs wr ->
      gder (A, eta ++ iota) (wl ++ wb ++ wr)
  | gd_term : forall A o, In (GTerm A o) G -> gder (A, []) (emit T o)
with gders : list N -> list T -> Prop :=
  | gds_nil : gders [] []
  | gds_cons : forall C Cs w1 w2,
      gder (C, []) w1 -> gders Cs w2 -> gders (C :: Cs) (w1 ++ w2).

Scheme gder_mut := Induction for gder Sort Prop
  with gders_mut := Induction for gders Sort Prop.

Lemma gders_app : forall Xs Ys u v, gders Xs u -> gders Ys v -> gders (Xs ++ Ys) (u ++ v).
Proof.
  intros Xs Ys u v H. revert Ys v. induction H; intros Ys v Hv; simpl.
  - exact Hv.
  - rewrite <- app_assoc. constructor; auto.
Qed.

Lemma gders_app_inv : forall Xs Ys w, gders (Xs ++ Ys) w ->
  exists u v, w = u ++ v /\ gders Xs u /\ gders Ys v.
Proof.
  induction Xs; intros Ys w H; simpl in H.
  - exists [], w. repeat split; auto. constructor.
  - inversion H; subst. destruct (IHXs _ _ H4) as [u [v [E [Hu Hv]]]]. subst.
    exists (w1 ++ u), v. repeat split.
    + apply app_assoc.
    + constructor; auto.
    + exact Hv.
Qed.

(* ---------------------------------------------------------------- *)
(* The normal-form grammar.  Fresh non-terminals Fr p st belong to   *)
(* the production with index p; the stage st records progress        *)
(* through its chain.                                                *)
(* ---------------------------------------------------------------- *)
Inductive stage : Type := SPop (l : nat) | SPush (l : nat) | SLeft (l : nat) | SRight (l : nat).
Inductive nt' : Type := Orig (A : N) | Fr (p : nat) (st : stage).

Notation lr := (lrule T nt' I).

Fixpoint pops (p l : nat) (ys : list I) : list lr :=
  match ys with
  | [] => []
  | i :: ys' => LPop _ _ _ (Fr p (SPop l)) i (Fr p (SPop (S l))) :: pops p (S l) ys'
  end.

Fixpoint pushes (p l : nat) (xs : list I) : list lr :=
  match xs with
  | [] => []
  | i :: xs' => LPush _ _ _ (Fr p (SPush l)) i (Fr p (SPush (S l))) :: pushes p (S l) xs'
  end.

Fixpoint lefts (p l : nat) (Cs : list N) : list lr :=
  match Cs with
  | [] => []
  | C :: Cs' => LInhR _ _ _ (Fr p (SLeft l)) (Orig C) (Fr p (SLeft (S l))) :: lefts p (S l) Cs'
  end.

Fixpoint rights (p l : nat) (Cs : list N) : list lr :=
  match Cs with
  | [] => []
  | C :: Cs' => LInhL _ _ _ (Fr p (SRight l)) (Fr p (SRight (S l))) (Orig C) :: rights p (S l) Cs'
  end.

Definition chain (p : nat) (q : gprod) : list lr :=
  match q with
  | GProd A eta Ls B eta' Rs =>
      [LChain _ _ _ (Orig A) (Fr p (SPop 0))] ++ pops p 0 eta ++
      [LChain _ _ _ (Fr p (SPop (length eta))) (Fr p (SPush 0))] ++ pushes p 0 (rev eta') ++
      [LChain _ _ _ (Fr p (SPush (length eta'))) (Fr p (SLeft 0))] ++ lefts p 0 Ls ++
      [LChain _ _ _ (Fr p (SLeft (length Ls))) (Fr p (SRight 0))] ++ rights p 0 (rev Rs) ++
      [LChain _ _ _ (Fr p (SRight (length Rs))) (Orig B)]
  | GTerm A o => [LTerm _ _ _ (Orig A) o]
  end.

Fixpoint conv (p : nat) (Gs : list gprod) : list lr :=
  match Gs with
  | [] => []
  | q :: Gs' => chain p q ++ conv (S p) Gs'
  end.

Definition G' : list lr := conv 0 G.

Notation nder := (nf_der T nt' I G').

(* ---------------- Membership ------------------------------------- *)

Lemma in_conv : forall Gs p0 r, In r (conv p0 Gs) ->
  exists p q, nth_error Gs p = Some q /\ In r (chain (p0 + p) q).
Proof.
  induction Gs; intros p0 r H; simpl in H; [contradiction |].
  apply in_app_iff in H. destruct H as [H | H].
  - exists 0, a. rewrite Nat.add_0_r. auto.
  - destruct (IHGs _ _ H) as [p [q [E Hq]]]. exists (S p), q.
    simpl. rewrite <- Nat.add_succ_comm. auto.
Qed.

Lemma conv_in : forall Gs p0 p q r, nth_error Gs p = Some q ->
  In r (chain (p0 + p) q) -> In r (conv p0 Gs).
Proof.
  induction Gs; intros p0 [|p] q r E H; simpl in E; try discriminate.
  - inversion E; subst. simpl. apply in_app_iff. left. rewrite Nat.add_0_r in H. exact H.
  - simpl. apply in_app_iff. right. apply (IHGs (S p0) p q); auto.
    rewrite Nat.add_succ_comm. exact H.
Qed.

Lemma in_G' : forall p q r, nth_error G p = Some q -> In r (chain p q) -> In r G'.
Proof. intros. apply (conv_in G 0 p q); auto. Qed.

Lemma in_pops : forall p ys l r, In r (pops p l ys) ->
  exists j i, nth_error ys j = Some i /\ r = LPop _ _ _ (Fr p (SPop (l + j))) i (Fr p (SPop (S (l + j)))).
Proof.
  induction ys; intros l r H; simpl in H; [contradiction |].
  destruct H as [H | H].
  - exists 0, a. rewrite Nat.add_0_r. auto.
  - destruct (IHys _ _ H) as [j [i [E Er]]]. exists (S j), i. split; [exact E |].
    rewrite Er. do 2 f_equal; [f_equal | do 2 f_equal]; lia.
Qed.

Lemma in_pushes : forall p xs l r, In r (pushes p l xs) ->
  exists j i, nth_error xs j = Some i /\ r = LPush _ _ _ (Fr p (SPush (l + j))) i (Fr p (SPush (S (l + j)))).
Proof.
  induction xs; intros l r H; simpl in H; [contradiction |].
  destruct H as [H | H].
  - exists 0, a. rewrite Nat.add_0_r. auto.
  - destruct (IHxs _ _ H) as [j [i [E Er]]]. exists (S j), i. split; [exact E |].
    rewrite Er. do 2 f_equal; [f_equal | do 2 f_equal]; lia.
Qed.

Lemma in_lefts : forall p Cs l r, In r (lefts p l Cs) ->
  exists j C, nth_error Cs j = Some C /\ r = LInhR _ _ _ (Fr p (SLeft (l + j))) (Orig C) (Fr p (SLeft (S (l + j)))).
Proof.
  induction Cs; intros l r H; simpl in H; [contradiction |].
  destruct H as [H | H].
  - exists 0, a. rewrite Nat.add_0_r. auto.
  - destruct (IHCs _ _ H) as [j [C [E Er]]]. exists (S j), C. split; [exact E |].
    rewrite Er. f_equal; [do 2 f_equal | do 2 f_equal]; lia.
Qed.

Lemma in_rights : forall p Cs l r, In r (rights p l Cs) ->
  exists j C, nth_error Cs j = Some C /\ r = LInhL _ _ _ (Fr p (SRight (l + j))) (Fr p (SRight (S (l + j)))) (Orig C).
Proof.
  induction Cs; intros l r H; simpl in H; [contradiction |].
  destruct H as [H | H].
  - exists 0, a. rewrite Nat.add_0_r. auto.
  - destruct (IHCs _ _ H) as [j [C [E Er]]]. exists (S j), C. split; [exact E |].
    rewrite Er. f_equal; do 2 f_equal; lia.
Qed.

Lemma pops_in : forall p ys l j i, nth_error ys j = Some i ->
  In (LPop _ _ _ (Fr p (SPop (l + j))) i (Fr p (SPop (S (l + j))))) (pops p l ys).
Proof.
  induction ys; intros l [|j] i E; simpl in E; try discriminate.
  - inversion E; subst. left. rewrite Nat.add_0_r. reflexivity.
  - right. replace (l + S j) with (S l + j) by lia. apply IHys. exact E.
Qed.

Lemma pushes_in : forall p xs l j i, nth_error xs j = Some i ->
  In (LPush _ _ _ (Fr p (SPush (l + j))) i (Fr p (SPush (S (l + j))))) (pushes p l xs).
Proof.
  induction xs; intros l [|j] i E; simpl in E; try discriminate.
  - inversion E; subst. left. rewrite Nat.add_0_r. reflexivity.
  - right. replace (l + S j) with (S l + j) by lia. apply IHxs. exact E.
Qed.

Lemma lefts_in : forall p Cs l j C, nth_error Cs j = Some C ->
  In (LInhR _ _ _ (Fr p (SLeft (l + j))) (Orig C) (Fr p (SLeft (S (l + j))))) (lefts p l Cs).
Proof.
  induction Cs; intros l [|j] C E; simpl in E; try discriminate.
  - inversion E; subst. left. rewrite Nat.add_0_r. reflexivity.
  - right. replace (l + S j) with (S l + j) by lia. apply IHCs. exact E.
Qed.

Lemma rights_in : forall p Cs l j C, nth_error Cs j = Some C ->
  In (LInhL _ _ _ (Fr p (SRight (l + j))) (Fr p (SRight (S (l + j)))) (Orig C)) (rights p l Cs).
Proof.
  induction Cs; intros l [|j] C E; simpl in E; try discriminate.
  - inversion E; subst. left. rewrite Nat.add_0_r. reflexivity.
  - right. replace (l + S j) with (S l + j) by lia. apply IHCs. exact E.
Qed.

(* ---------------- List helpers ------------------------------------ *)

Lemma skipn_cons_nth : forall {X} (xs : list X) l y ys,
  skipn l xs = y :: ys -> nth_error xs l = Some y /\ skipn (S l) xs = ys.
Proof.
  intros X xs. induction xs; intros [|l] y ys E; simpl in E; try discriminate.
  - inversion E; subst. auto.
  - simpl. apply IHxs. exact E.
Qed.

Lemma nth_skipn : forall {X} (xs : list X) l y,
  nth_error xs l = Some y -> skipn l xs = y :: skipn (S l) xs.
Proof.
  intros X xs. induction xs; intros [|l] y E; simpl in E; try discriminate.
  - inversion E; subst. reflexivity.
  - simpl. apply IHxs. exact E.
Qed.

Lemma skipn_nil_len : forall {X} (xs : list X) l,
  skipn l xs = [] -> l <= length xs -> l = length xs.
Proof.
  intros X xs l E Hl. pose proof (skipn_length l xs) as Hs. rewrite E in Hs. simpl in Hs. lia.
Qed.

Lemma skipn_len : forall {X} (xs : list X), skipn (length xs) xs = [].
Proof. intros. apply skipn_all. Qed.

Lemma skipn_cons_le : forall {X} (xs : list X) l y ys,
  skipn l xs = y :: ys -> S l <= length xs.
Proof.
  intros X xs l y ys E. pose proof (skipn_length l xs) as Hs. rewrite E in Hs. simpl in Hs. lia.
Qed.

(* Strings of a list of categories, concatenated in reverse list order. *)
Inductive grs : list N -> list T -> Prop :=
  | grs_nil : grs [] []
  | grs_cons : forall C Cs u v, grs Cs u -> gder (C, []) v -> grs (C :: Cs) (u ++ v).

Lemma grs_gders : forall ys w, grs ys w -> gders (rev ys) w.
Proof.
  intros ys w H; induction H; simpl.
  - constructor.
  - apply gders_app; [exact IHgrs |]. rewrite <- (app_nil_r v). constructor; [exact H0 | constructor].
Qed.

(* ---------------- Soundness: G'  ==>  G ------------------------------ *)

Definition meaning (c : nt' * list I) (w : list T) : Prop :=
  match c with
  | (Orig A, sigma) => gder (A, sigma) w
  | (Fr p st, sigma) =>
      match nth_error G p with
      | Some (GProd A eta Ls B eta' Rs) =>
          match st with
          | SPop l => exists iota, sigma = skipn l eta ++ iota /\
              exists wl wb wr, w = wl ++ wb ++ wr /\ gders Ls wl /\
                gder (B, eta' ++ iota) wb /\ gders Rs wr
          | SPush l => exists wl wb wr, w = wl ++ wb ++ wr /\ gders Ls wl /\
              gder (B, rev (skipn l (rev eta')) ++ sigma) wb /\ gders Rs wr
          | SLeft l => exists wl wb wr, w = wl ++ wb ++ wr /\ gders (skipn l Ls) wl /\
              gder (B, sigma) wb /\ gders Rs wr
          | SRight l => exists wb wr, w = wb ++ wr /\ gder (B, sigma) wb /\
              grs (skipn l (rev Rs)) wr
          end
      | _ => True
      end
  end.

Ltac classify H :=
  let p := fresh "p" in let q := fresh "q" in let E := fresh "E" in let Hq := fresh "Hq" in
  destruct (in_conv G 0 _ H) as [p [q [E Hq]]]; simpl in Hq;
  destruct q as [?A ?eta ?Ls ?B ?eta' ?Rs | ?A ?o]; simpl in Hq;
  repeat match type of Hq with
  | _ \/ _ => destruct Hq as [Hq | Hq]
  | False => contradiction
  | In _ (_ ++ _) => apply in_app_iff in Hq
  | In _ (_ :: _) => simpl in Hq
  | In _ [] => contradiction
  | In _ (pops _ _ _) =>
      let j := fresh "j" in let i := fresh "i" in let Ej := fresh "Ej" in let Hq' := fresh "Hq" in
      destruct (in_pops _ _ _ _ Hq) as [j [i [Ej Hq']]]; clear Hq; rename Hq' into Hq
  | In _ (pushes _ _ _) =>
      let j := fresh "j" in let i := fresh "i" in let Ej := fresh "Ej" in let Hq' := fresh "Hq" in
      destruct (in_pushes _ _ _ _ Hq) as [j [i [Ej Hq']]]; clear Hq; rename Hq' into Hq
  | In _ (lefts _ _ _) =>
      let j := fresh "j" in let C := fresh "C" in let Ej := fresh "Ej" in let Hq' := fresh "Hq" in
      destruct (in_lefts _ _ _ _ Hq) as [j [C [Ej Hq']]]; clear Hq; rename Hq' into Hq
  | In _ (rights _ _ _) =>
      let j := fresh "j" in let C := fresh "C" in let Ej := fresh "Ej" in let Hq' := fresh "Hq" in
      destruct (in_rights _ _ _ _ Hq) as [j [C [Ej Hq']]]; clear Hq; rename Hq' into Hq
  end;
  try discriminate Hq;
  try (inversion Hq; subst; clear Hq).

Ltac mn := unfold meaning in *; cbv beta iota in *;
  try (match goal with h : nth_error G _ = Some _ |- _ => rewrite h in * end);
  cbv beta iota in *.

Lemma soundness : forall c w t, nder c w t -> meaning c w.
Proof.
  intros c w t H; induction H.
  - (* LInhL: only the right-sister peeling *)
    classify H; mn.
    destruct IHnf_der1 as [wb [wr [Ew [HB Hr]]]]. subst.
    exists wb, (wr ++ w2). split; [rewrite <- app_assoc; reflexivity |]. split; [exact HB |].
    rewrite (nth_skipn _ _ _ Ej). constructor; assumption.
  - (* LInhR: only the left-sister peeling *)
    classify H; mn.
    destruct IHnf_der2 as [wl [wb [wr [Ew [Hl [HB Hr]]]]]]. subst.
    exists (w1 ++ wl), wb, wr. repeat split; auto.
    + rewrite <- app_assoc. reflexivity.
    + rewrite (nth_skipn _ _ _ Ej). constructor; assumption.
  - (* LPush *)
    classify H; mn.
    destruct IHnf_der as [wl [wb [wr [Ew [Hl [HB Hr]]]]]]. subst.
    exists wl, wb, wr. repeat split; auto.
    rewrite (nth_skipn _ _ _ Ej). simpl. rewrite <- app_assoc. exact HB.
  - (* LPop *)
    classify H; mn.
    destruct IHnf_der as [iota [Es Hf]]. subst.
    exists iota. split; [| exact Hf].
    rewrite (nth_skipn _ _ _ Ej). reflexivity.
  - (* LChain *)
    classify H; mn.
    + (* Orig A -> SPop 0 *)
      destruct IHnf_der as [iota [Es [wl [wb [wr [Ew [Hl [HB Hr]]]]]]]]. subst.
      simpl. eapply gd_prod; [eapply nth_error_In; eassumption | eassumption | eassumption | eassumption].
    + (* SPop |eta| -> SPush 0 *)
      destruct IHnf_der as [wl [wb [wr [Ew [Hl [HB Hr]]]]]]. subst.
      exists ix. rewrite skipn_len. split; [reflexivity |].
      exists wl, wb, wr. simpl skipn in HB. rewrite rev_involutive in HB. auto.
    + (* SPush |eta'| -> SLeft 0 *)
      destruct IHnf_der as [wl [wb [wr [Ew [Hl [HB Hr]]]]]]. subst.
      exists wl, wb, wr. rewrite <- (rev_length eta'), skipn_len. simpl. auto.
    + (* SLeft |Ls| -> SRight 0 *)
      destruct IHnf_der as [wb [wr [Ew [HB Hr]]]]. subst.
      exists [], wb, wr. rewrite skipn_len. simpl.
      repeat split; auto; [constructor |].
      simpl skipn in Hr. apply grs_gders in Hr. rewrite rev_involutive in Hr. exact Hr.
    + (* SRight |Rs| -> Orig B *)
      exists w, []. rewrite <- (rev_length Rs), skipn_len. rewrite app_nil_r.
      repeat split; auto. constructor.
  - (* LTerm *)
    classify H; mn. apply gd_term. eapply nth_error_In. eassumption.
Qed.

(* ---------------- Completeness: G  ==>  G' ------------------------ *)

Inductive nrs : list N -> list T -> Prop :=
  | nrs_nil : nrs [] []
  | nrs_cons : forall C Cs u v t, nrs Cs u -> nder (Orig C, []) v t -> nrs (C :: Cs) (u ++ v).

Inductive nds : list N -> list T -> Prop :=
  | nds_nil : nds [] []
  | nds_cons : forall C Cs u v t, nder (Orig C, []) u t -> nds Cs v -> nds (C :: Cs) (u ++ v).

Lemma nrs_snoc : forall ys u C v t, nrs ys u -> nder (Orig C, []) v t -> nrs (ys ++ [C]) (v ++ u).
Proof.
  intros ys u C v t H. revert C v t. induction H; intros C' v' t' Hv; simpl.
  - rewrite app_nil_r. change (nrs [C'] ([] ++ v')).
    exact (nrs_cons C' [] [] v' t' nrs_nil Hv).
  - rewrite app_assoc. exact (nrs_cons C (Cs ++ [C']) (v' ++ u) v t (IHnrs C' v' t' Hv) H0).
Qed.

Lemma nds_nrs : forall Xs w, nds Xs w -> nrs (rev Xs) w.
Proof.
  intros Xs w H; induction H; simpl.
  - constructor.
  - eapply nrs_snoc; eauto.
Qed.

Section Chain.
Variables (p : nat) (A : N) (eta : list I) (Ls : list N) (B : N) (eta' : list I) (Rs : list N).
Hypothesis Hp : nth_error G p = Some (GProd A eta Ls B eta' Rs).

Lemma inq : forall r, In r (chain p (GProd A eta Ls B eta' Rs)) -> In r G'.
Proof. intros r. apply (in_G' p _ r Hp). Qed.

Ltac inchain := apply inq; simpl; repeat (rewrite in_app_iff; simpl).

Lemma right_stage : forall ys l sigma wb tb wr,
  skipn l (rev Rs) = ys -> l <= length Rs ->
  nder (Orig B, sigma) wb tb -> nrs ys wr ->
  exists t, nder (Fr p (SRight l), sigma) (wb ++ wr) t.
Proof.
  induction ys as [| C ys IH]; intros l sigma wb tb wr Hs Hl HB Hr.
  - inversion Hr; subst. rewrite app_nil_r.
    apply skipn_nil_len in Hs; [| rewrite rev_length; exact Hl]. rewrite rev_length in Hs. subst.
    eexists. eapply n_chain; [| exact HB]; inchain; intuition.
  - inversion Hr as [| C' ys' u v t Hu Hv]; subst. destruct (skipn_cons_nth _ _ _ _ Hs) as [En Es].
    pose proof (skipn_cons_le _ _ _ _ Hs) as Hle. rewrite rev_length in Hle.
    destruct (IH (S l) sigma wb tb u Es Hle HB Hu) as [t1 H1].
    eexists. rewrite app_assoc. eapply n_inhl; [| exact H1 | exact Hv].
    pose proof (rights_in p (rev Rs) 0 l C En) as Hin; simpl in Hin; inchain; intuition.
Qed.

Lemma left_stage : forall Cs l sigma w' t' wl,
  skipn l Ls = Cs -> l <= length Ls ->
  nder (Fr p (SRight 0), sigma) w' t' -> nds Cs wl ->
  exists t, nder (Fr p (SLeft l), sigma) (wl ++ w') t.
Proof.
  induction Cs as [| C Cs IH]; intros l sigma w' t' wl Hs Hl HR Hn.
  - inversion Hn; subst. apply skipn_nil_len in Hs; [| exact Hl]. subst.
    eexists. eapply n_chain; [| exact HR]; inchain; intuition.
  - inversion Hn as [| C' Cs' u v t Hu Hv]; subst. destruct (skipn_cons_nth _ _ _ _ Hs) as [En Es].
    pose proof (skipn_cons_le _ _ _ _ Hs) as Hle.
    destruct (IH (S l) sigma w' t' v Es Hle HR Hv) as [t1 H1].
    eexists. rewrite <- app_assoc. eapply n_inhr; [| exact Hu | exact H1].
    pose proof (lefts_in p Ls 0 l C En) as Hin; simpl in Hin; inchain; intuition.
Qed.

Lemma push_stage : forall xs l tau w t,
  skipn l (rev eta') = xs -> l <= length eta' ->
  nder (Fr p (SLeft 0), rev xs ++ tau) w t ->
  exists t', nder (Fr p (SPush l), tau) w t'.
Proof.
  induction xs as [| x xs IH]; intros l tau w t Hs Hl HL.
  - apply skipn_nil_len in Hs; [| rewrite rev_length; exact Hl]. rewrite rev_length in Hs. subst.
    eexists. eapply n_chain; [| exact HL]; inchain; intuition.
  - destruct (skipn_cons_nth _ _ _ _ Hs) as [En Es].
    pose proof (skipn_cons_le _ _ _ _ Hs) as Hle. rewrite rev_length in Hle.
    simpl in HL. rewrite <- app_assoc in HL. simpl in HL.
    destruct (IH (S l) (x :: tau) w t Es Hle HL) as [t1 H1].
    eexists. eapply n_push; [| exact H1].
    pose proof (pushes_in p (rev eta') 0 l x En) as Hin; simpl in Hin; inchain; intuition.
Qed.

Lemma pop_stage : forall ys l iota w t,
  skipn l eta = ys -> l <= length eta ->
  nder (Fr p (SPush 0), iota) w t ->
  exists t', nder (Fr p (SPop l), ys ++ iota) w t'.
Proof.
  induction ys as [| y ys IH]; intros l iota w t Hs Hl HP.
  - apply skipn_nil_len in Hs; [| exact Hl]. subst.
    eexists. eapply n_chain; [| exact HP]; inchain; intuition.
  - destruct (skipn_cons_nth _ _ _ _ Hs) as [En Es].
    pose proof (skipn_cons_le _ _ _ _ Hs) as Hle.
    destruct (IH (S l) iota w t Es Hle HP) as [t1 H1].
    eexists. simpl. eapply n_pop; [| exact H1].
    pose proof (pops_in p eta 0 l y En) as Hin; simpl in Hin; inchain; intuition.
Qed.

Lemma chain_complete : forall iota wl wb wr tb,
  nds Ls wl -> nder (Orig B, eta' ++ iota) wb tb -> nds Rs wr ->
  exists t, nder (Orig A, eta ++ iota) (wl ++ wb ++ wr) t.
Proof.
  intros iota wl wb wr tb Hl HB Hr.
  destruct (right_stage (rev Rs) 0 _ _ _ _ eq_refl (Nat.le_0_l _) HB (nds_nrs _ _ Hr)) as [t1 H1].
  destruct (left_stage Ls 0 _ _ _ _ eq_refl (Nat.le_0_l _) H1 Hl) as [t2 H2].
  rewrite <- (rev_involutive eta') in H2.
  destruct (push_stage (rev eta') 0 iota _ _ eq_refl (Nat.le_0_l _) H2) as [t3 H3].
  destruct (pop_stage eta 0 iota _ _ eq_refl (Nat.le_0_l _) H3) as [t4 H4].
  eexists. eapply n_chain; [| exact H4]; inchain; intuition.
Qed.

End Chain.

Lemma completeness : forall c w, gder c w -> exists t, nder (Orig (fst c), snd c) w t.
Proof.
  apply (gder_mut (fun c w _ => exists t, nder (Orig (fst c), snd c) w t)
                  (fun Cs w _ => nds Cs w)).
  - intros A eta Ls B eta' Rs iota wl wb wr Hin Hls IHls HB IHB Hrs IHrs. simpl in *.
    destruct IHB as [tb HB']. destruct (In_nth_error _ _ Hin) as [p Hp].
    exact (chain_complete p A eta Ls B eta' Rs Hp iota wl wb wr tb IHls HB' IHrs).
  - intros A o Hin. destruct (In_nth_error _ _ Hin) as [p Hp].
    eexists. apply n_term. apply (in_G' p _ _ Hp). simpl. left. reflexivity.
  - constructor.
  - intros C Cs w1 w2 H IH H' IH'. simpl in IH. destruct IH as [t Ht].
    econstructor; eauto.
Qed.

(* Lemma 9: G and its normal form G' generate the same language. *)
Theorem lig_normal_form : forall S w,
  gder (S, []) w <-> exists t, nder (Orig S, []) w t.
Proof.
  intros S w; split.
  - intro H. exact (completeness _ _ H).
  - intros [t H]. exact (soundness _ _ _ H).
Qed.

(* Hence every LIG language is generated by an indexed path grammar:
   the canonical IPG of the normal form G'. *)
Corollary lig_to_ipg_language : forall S w,
  gder (S, []) w <->
  exists t, derives T nt' I (IP T nt' I G') ([], FNT T nt' I (Orig S, [])) w ([], FT T nt' I t).
Proof.
  intros S w. rewrite lig_normal_form. split; intros [t H]; exists t.
  - apply lig_ipg_equivalence. exact H.
  - apply lig_ipg_equivalence in H. exact H.
Qed.

End NormalForm.
