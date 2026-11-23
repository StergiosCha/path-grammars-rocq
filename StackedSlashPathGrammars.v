(* ===================================================================== *)
(*  Stacked-Slash Path Grammars                                          *)
(*                                                                       *)
(*  A slashed category carries a stack of pending fillers, each with its *)
(*  term.  Binary rules fix the routing of the filler stack (path, def   *)
(*  or split), fronting licences may change the category, and gap sites  *)
(*  say which categories may host the gap of which filler.               *)
(*                                                                       *)
(*  Checked with Coq 8.18:                                               *)
(*    coqc ExtendedPathGrammars.v                                        *)
(*    coqc -Q . "" StackedSlashPathGrammars.v                            *)
(* ===================================================================== *)

Require Import List.
Import ListNotations.
Require Import Permutation.
Require ExtendedPathGrammars.

Local Arguments ExtendedPathGrammars.Leaf {terminal}.
Local Arguments ExtendedPathGrammars.Node {terminal}.
Local Arguments ExtendedPathGrammars.LinkT {terminal}.

Section Stacked.

Variables terminal nonterminal : Type.

(* Terms are those of the extended development: leaves, pairs and LINKed
   trees. *)
Notation term := (ExtendedPathGrammars.term terminal).
Notation Leaf := ExtendedPathGrammars.Leaf.
Notation Node := ExtendedPathGrammars.Node.
Notation LinkT := ExtendedPathGrammars.LinkT.

Inductive route : Type := Path | Def | Split.

Inductive rule : Type :=
  | PRule : nonterminal -> nonterminal -> nonterminal -> route -> rule
      (* PRule A B C r : A ->r [B] C, with path daughter C and deferred B *)
  | TRule : nonterminal -> terminal -> rule
      (* A -> a *)
  | TopRule : nonterminal -> nonterminal -> nonterminal -> rule
      (* TopRule A D B : a D may be fronted out of an A, which continues as B *)
  | GapRule : nonterminal -> nonterminal -> rule
      (* GapRule G D : a G may be the gap of a D-filler *)
  | LRule : nonterminal -> nonterminal -> nonterminal -> nonterminal -> rule.
      (* LRule A D C B : A -> [LINK_D(C)] B *)

(* A filler stack lists its entries top first. *)
Definition fstack : Type := list (nonterminal * term).

Inductive ssym : Type :=
  | SCat : nonterminal -> fstack -> ssym          (* B/gamma   *)
  | SLink : nonterminal -> nonterminal -> ssym.   (* LINK_D(C) *)

Inductive focus : Type :=
  | FCat : nonterminal -> fstack -> focus         (* A/gamma   *)
  | FT : term -> focus.

Definition item : Type := (list ssym * focus)%type.

Variable R : list rule.

Inductive derives : item -> list terminal -> item -> Prop :=
  | d_refl : forall c, derives c [] c
  (* RW1, routing "path": the whole stack goes to the path daughter *)
  | d_path : forall X A B C g s c',
      In (PRule A B C Path) R ->
      derives (SCat B [] :: X, FCat C g) s c' ->
      derives (X, FCat A g) s c'
  (* RW1, routing "def": the whole stack goes to the deferred daughter *)
  | d_def : forall X A B C g s c',
      In (PRule A B C Def) R ->
      derives (SCat B g :: X, FCat C []) s c' ->
      derives (X, FCat A g) s c'
  (* RW1, routing "split": the top filler goes to the deferred daughter,
     the rest of the stack to the path daughter *)
  | d_split : forall X A B C D al g s c',
      In (PRule A B C Split) R ->
      derives (SCat B [(D, al)] :: X, FCat C g) s c' ->
      derives (X, FCat A ((D, al) :: g)) s c'
  (* RW2: scan, plain categories only *)
  | d_rw2 : forall X A a s c',
      In (TRule A a) R ->
      derives (X, FT (Leaf a)) s c' ->
      derives (X, FCat A []) (a :: s) c'
  (* RW3: pop *)
  | d_rw3 : forall X B g t tB s1 s2 c',
      derives ([], FCat B g) s1 ([], FT tB) ->
      derives (X, FT (Node t tB)) s2 c' ->
      derives (SCat B g :: X, FT t) (s1 ++ s2) c'
  (* RW4: fronting; the filler is derived from a plain D and pushed *)
  | d_rw4 : forall X A D B g al s1 s2 c',
      In (TopRule A D B) R ->
      derives ([], FCat D []) s1 ([], FT al) ->
      derives (X, FCat B ((D, al) :: g)) s2 c' ->
      derives (X, FCat A g) (s1 ++ s2) c'
  (* RW6: a gap site with a single pending filler is filled by it *)
  | d_rw6 : forall X G D al s c',
      In (GapRule G D) R ->
      derives (X, FT al) s c' ->
      derives (X, FCat G [(D, al)]) s c'
  (* RW7: LINK introduction, plain categories only *)
  | d_rw7 : forall X A D C B s c',
      In (LRule A D C B) R ->
      derives (SLink D C :: X, FCat B []) s c' ->
      derives (X, FCat A []) s c'
  (* RW8: LINK resolution; the linked C starts with a fresh stack holding
     only a copy of the host *)
  | d_rw8 : forall X D C t tL s1 s2 c',
      derives ([], FCat C [(D, t)]) s1 ([], FT tL) ->
      derives (X, FT (Node t (LinkT tL))) s2 c' ->
      derives (SLink D C :: X, FT t) (s1 ++ s2) c'.

Definition ssg_language (S : nonterminal) (w : list terminal) : Prop :=
  exists t, derives ([], FCat S []) w ([], FT t).

Lemma derives_trans : forall c1 s1 c2 s2 c3,
  derives c1 s1 c2 -> derives c2 s2 c3 -> derives c1 (s1 ++ s2) c3.
Proof.
  intros c1 s1 c2 s2 c3 H1 H2.
  induction H1.
  - exact H2.
  - eapply d_path; eauto.
  - eapply d_def; eauto.
  - eapply d_split; eauto.
  - simpl. eapply d_rw2; eauto.
  - rewrite <- app_assoc. eapply d_rw3; eauto.
  - rewrite <- app_assoc. eapply d_rw4; eauto.
  - eapply d_rw6; eauto.
  - eapply d_rw7; eauto.
  - rewrite <- app_assoc. eapply d_rw8; eauto.
Qed.

(* ===================================================================== *)
(*  Upper bound: a linear indexed grammar G-natural with the same         *)
(*  strings.  Filler terms are erased, and the category of each filler   *)
(*  becomes an index.                                                     *)
(* ===================================================================== *)

(* The non-terminal alphabet is finite. *)
Variable allN : list nonterminal.
Hypothesis allN_complete : forall A : nonterminal, In A allN.

(* Non-terminals of G-natural. *)
Inductive lnt : Type :=
  | LN : nonterminal -> lnt                     (* A                         *)
  | LB : nonterminal -> nonterminal -> lnt      (* B^D: B with D pushed      *)
  | LK : nonterminal -> nonterminal -> nonterminal -> nonterminal -> lnt
                                                (* A'' for a LINK rule       *)
  | LZ : lnt.                                   (* Z, with Z[] -> epsilon     *)

(* LIG productions.  LP A pop L B push Rt is
     A[.. pop] -> L[]  B[.. push]  Rt[],
   with the distinguished daughter B in the middle (index stacks list their
   top first).  The side daughters can be LZ, which derives only the empty
   string.  LT A (Some a) is A[] -> a, and LT A None is A[] -> epsilon. *)
Inductive lprod : Type :=
  | LP : lnt -> list nonterminal -> lnt -> lnt -> list nonterminal -> lnt -> lprod
  | LT : lnt -> option terminal -> lprod.

Section LIG.

Variable P : list lprod.

Inductive lder : lnt -> list nonterminal -> list terminal -> Prop :=
  | l_term : forall A a, In (LT A (Some a)) P -> lder A [] [a]
  | l_eps : forall A, In (LT A None) P -> lder A [] []
  | l_prod : forall A pop L B push Rt g w1 w2 w3,
      In (LP A pop L B push Rt) P ->
      lder L [] w1 -> lder B (push ++ g) w2 -> lder Rt [] w3 ->
      lder A (pop ++ g) (w1 ++ w2 ++ w3).

End LIG.

(* The productions contributed by each rule of the path grammar. *)
Definition nat_rule (r : rule) : list lprod :=
  match r with
  | PRule A B C Path => [LP (LN A) [] LZ (LN C) [] (LN B)]
  | PRule A B C Def => [LP (LN A) [] (LN C) (LN B) [] LZ]
  | PRule A B C Split =>
      map (fun D => LP (LN A) [D] LZ (LN C) [] (LB B D)) allN
  | TRule A a => [LT (LN A) (Some a)]
  | TopRule A D B => [LP (LN A) [] (LN D) (LN B) [D] LZ]
  | GapRule G D => [LP (LN G) [D] LZ LZ [] LZ]
  | LRule A D C B =>
      [LP (LN A) [] LZ LZ [] (LK A D C B); LP (LK A D C B) [] (LN B) (LB C D) [] LZ]
  end.

Definition natural : list lprod :=
  LT LZ None
  :: map (fun BD => LP (LB (fst BD) (snd BD)) [] LZ (LN (fst BD)) [snd BD] LZ)
         (list_prod allN allN)
  ++ flat_map nat_rule R.

Definition lig_language (S : nonterminal) (w : list terminal) : Prop :=
  lder natural (LN S) [] w.

Lemma in_nat_rule : forall r p, In r R -> In p (nat_rule r) -> In p natural.
Proof.
  intros r p Hr Hp. unfold natural. right. apply in_or_app. right.
  apply in_flat_map. eauto.
Qed.

Lemma in_natural_LB : forall B D,
  In (LP (LB B D) [] LZ (LN B) [D] LZ) natural.
Proof.
  intros B D. unfold natural. right. apply in_or_app. left.
  apply (in_map (fun BD => LP (LB (fst BD) (snd BD)) [] LZ (LN (fst BD)) [snd BD] LZ)
                _ (B, D)).
  apply in_prod; apply allN_complete.
Qed.

Lemma in_natural_Z : In (LT LZ None) natural.
Proof. left. reflexivity. Qed.

(* ---------------- Soundness: path grammar ==> G-natural ------------- *)

Definition pcat : Type := (lnt * list nonterminal)%type.

Definition scat (x : ssym) : pcat :=
  match x with
  | SCat B g => (LN B, map fst g)
  | SLink D C => (LN C, [D])
  end.

Inductive lders : list pcat -> list terminal -> Prop :=
  | ls_nil : lders [] []
  | ls_cons : forall A g cs w1 w2,
      lder natural A g w1 -> lders cs w2 -> lders ((A, g) :: cs) (w1 ++ w2).

Definition pending (c : item) : list pcat :=
  match c with
  | (X, FCat A g) => (LN A, map fst g) :: map scat X
  | (X, FT _) => map scat X
  end.

Lemma lders_inv : forall A g cs w, lders ((A, g) :: cs) w ->
  exists w1 w2, w = w1 ++ w2 /\ lder natural A g w1 /\ lders cs w2.
Proof. intros A g cs w H. inversion H; subst. eauto. Qed.

Lemma lders_one : forall A g w, lders [(A, g)] w -> lder natural A g w.
Proof.
  intros A g w H. destruct (lders_inv _ _ _ _ H) as [w1 [w2 [E [H1 H2]]]].
  inversion H2; subst. rewrite app_nil_r. exact H1.
Qed.

Lemma sub_lder : forall A g s t,
  (forall w, lders (pending ([], FT t)) w -> lders (pending ([], FCat A g)) (s ++ w)) ->
  lder natural (LN A) (map fst g) s.
Proof.
  intros A g s t H. apply lders_one. rewrite <- (app_nil_r s). apply H. constructor.
Qed.

Lemma lder_Z : lder natural LZ [] [].
Proof. apply l_eps. apply in_natural_Z. Qed.

Lemma l_app : forall A pop L B push Rt g g1 g2 w1 w2 w3 w,
  In (LP A pop L B push Rt) natural ->
  lder natural L [] w1 -> lder natural B g2 w2 -> lder natural Rt [] w3 ->
  g2 = push ++ g -> g1 = pop ++ g -> w = w1 ++ w2 ++ w3 ->
  lder natural A g1 w.
Proof. intros; subst; eapply l_prod; eauto. Qed.

Lemma l_LB : forall B D w, lder natural (LN B) [D] w -> lder natural (LB B D) [] w.
Proof.
  intros B D w H. eapply l_app with (g := []);
    [apply in_natural_LB | apply lder_Z | exact H | apply lder_Z | reflexivity | reflexivity |].
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma derives_pending : forall c s c',
  derives c s c' -> forall w, lders (pending c') w -> lders (pending c) (s ++ w).
Proof.
  intros c s c' H; induction H; intros w Hw; simpl in *.
  - exact Hw.
  - (* path *)
    destruct (lders_inv _ _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (lders_inv _ _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    rewrite E, E', app_assoc. constructor; [| exact Hr'].
    eapply l_app with (g := map fst g);
      [eapply in_nat_rule; [eassumption | left; reflexivity]
      | apply lder_Z | exact HC | exact HB | reflexivity | reflexivity | reflexivity].
  - (* def *)
    destruct (lders_inv _ _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (lders_inv _ _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    rewrite E, E', app_assoc. constructor; [| exact Hr'].
    eapply l_app with (g := map fst g);
      [eapply in_nat_rule; [eassumption | left; reflexivity]
      | exact HC | exact HB | apply lder_Z | reflexivity | reflexivity |].
    rewrite app_nil_r. reflexivity.
  - (* split *)
    destruct (lders_inv _ _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HC Hr]]]].
    destruct (lders_inv _ _ _ _ Hr) as [v1 [v2 [E' [HB Hr']]]].
    rewrite E, E', app_assoc. constructor; [| exact Hr'].
    eapply l_app with (pop := [D]) (L := LZ) (B := LN C) (push := []) (Rt := LB B D)
                      (g := map fst g);
      [| apply lder_Z | exact HC | apply l_LB; exact HB | reflexivity | reflexivity | reflexivity].
    eapply in_nat_rule; [eassumption |]. simpl.
    apply (in_map (fun D0 => LP (LN A) [D0] LZ (LN C) [] (LB B D0))). apply allN_complete.
  - (* RW2 *)
    change (a :: s ++ w) with ([a] ++ (s ++ w)).
    constructor; [| exact (IHderives w Hw)].
    apply l_term. eapply in_nat_rule; [eassumption | left; reflexivity].
  - (* RW3 *)
    pose proof (sub_lder _ _ _ tB IHderives1) as HB.
    rewrite <- app_assoc. constructor; [exact HB | exact (IHderives2 w Hw)].
  - (* RW4 *)
    pose proof (sub_lder D [] s1 al IHderives1) as HD. simpl in HD.
    destruct (lders_inv _ _ _ _ (IHderives2 w Hw)) as [u1 [u2 [E [HB Hr]]]].
    rewrite <- app_assoc, E, app_assoc. constructor; [| exact Hr].
    eapply l_app with (g := map fst g);
      [eapply in_nat_rule; [eassumption | left; reflexivity]
      | exact HD | exact HB | apply lder_Z | reflexivity | reflexivity |].
    rewrite app_nil_r. reflexivity.
  - (* RW6 *)
    change (s ++ w) with ([] ++ (s ++ w)).
    constructor; [| exact (IHderives w Hw)].
    eapply l_app with (g := []);
      [eapply in_nat_rule; [eassumption | left; reflexivity]
      | apply lder_Z | apply lder_Z | apply lder_Z | reflexivity | reflexivity | reflexivity].
  - (* RW7 *)
    destruct (lders_inv _ _ _ _ (IHderives w Hw)) as [u1 [u2 [E [HB Hr]]]].
    destruct (lders_inv _ _ _ _ Hr) as [v1 [v2 [E' [HL Hr']]]].
    rewrite E, E', app_assoc. constructor; [| exact Hr'].
    eapply l_app with (g := []);
      [eapply in_nat_rule; [eassumption | left; reflexivity]
      | apply lder_Z | apply lder_Z | | reflexivity | reflexivity | reflexivity].
    eapply l_app with (g := []);
      [eapply in_nat_rule; [eassumption | right; left; reflexivity]
      | exact HB | apply l_LB; exact HL | apply lder_Z | reflexivity | reflexivity |].
    rewrite app_nil_r. reflexivity.
  - (* RW8 *)
    pose proof (sub_lder C [(D, t)] s1 tL IHderives1) as HL. simpl in HL.
    rewrite <- app_assoc. constructor; [exact HL | exact (IHderives2 w Hw)].
Qed.

Lemma ssg_to_lig : forall S w t,
  derives ([], FCat S []) w ([], FT t) -> lder natural (LN S) [] w.
Proof.
  intros S w t H. apply lders_one.
  rewrite <- (app_nil_r w). apply (derives_pending _ _ _ H). constructor.
Qed.

(* ---------------- Completeness: G-natural ==> path grammar ---------- *)

Lemma in_natural_inv : forall p, In p natural ->
  p = LT LZ None \/
  (exists B D, p = LP (LB B D) [] LZ (LN B) [D] LZ) \/
  (exists r, In r R /\ In p (nat_rule r)).
Proof.
  intros p H. unfold natural in H. destruct H as [H | H]; [left; auto |].
  apply in_app_or in H. destruct H as [H | H].
  - right; left. apply in_map_iff in H. destruct H as [[B D] [E _]].
    exists B, D. symmetry. exact E.
  - right; right. apply in_flat_map in H. exact H.
Qed.

(* What a derivation of G-natural from each kind of non-terminal
   guarantees for the path grammar.  Filler terms are arbitrary. *)
Definition realisable (A : lnt) (g : list nonterminal) (w : list terminal) : Prop :=
  match A with
  | LN A => forall X gm, map fst gm = g ->
      exists t, derives (X, FCat A gm) w (X, FT t)
  | LB B D => forall X gm al, map fst gm = g ->
      exists t, derives (X, FCat B ((D, al) :: gm)) w (X, FT t)
  | LK A D C B => g = [] -> forall X,
      exists t, derives (SLink D C :: X, FCat B []) w (X, FT t)
  | LZ => g = [] /\ w = []
  end.

Lemma map_fst_nil : forall gm : fstack, map fst gm = [] -> gm = [].
Proof. intros [| x gm] H; [reflexivity | discriminate]. Qed.

Lemma map_fst_cons : forall (gm : fstack) D g, map fst gm = D :: g ->
  exists al gm', gm = (D, al) :: gm' /\ map fst gm' = g.
Proof.
  intros [| [D' al] gm] D g H; [discriminate |].
  simpl in H. injection H as E1 E2. subst. eauto.
Qed.

Lemma lig_to_ssg : forall A g w, lder natural A g w -> realisable A g w.
Proof.
  intros A g w H; induction H.
  - (* A[] -> a *)
    apply in_natural_inv in H.
    destruct H as [H | [[B [D H]] | [r [Hr Hp]]]]; try discriminate.
    destruct r as [A0 B C [] | A0 a0 | A0 D B | G D | A0 D C B]; simpl in Hp;
      try (apply in_map_iff in Hp; destruct Hp as [? [? _]]; discriminate);
      repeat (destruct Hp as [Hp | Hp]; [try discriminate | ]); try contradiction.
    injection Hp as E1 E2. subst.
    intros X gm Hg. apply map_fst_nil in Hg. subst.
    exists (Leaf a). rewrite <- (app_nil_r [a]). eapply d_rw2; [eassumption | apply d_refl].
  - (* A[] -> epsilon *)
    apply in_natural_inv in H.
    destruct H as [H | [[B [D H]] | [r [Hr Hp]]]]; try discriminate.
    + injection H as E. subst. simpl. auto.
    + destruct r as [A0 B C [] | A0 a0 | A0 D B | G D | A0 D C B]; simpl in Hp;
        try (apply in_map_iff in Hp; destruct Hp as [? [? _]]; discriminate);
        repeat (destruct Hp as [Hp | Hp]; [try discriminate | ]); try contradiction.
  - (* A[.. pop] -> L[] B[.. push] Rt[] *)
    apply in_natural_inv in H.
    destruct H as [H | [[B0 [D H]] | [r [Hr Hp]]]]; try discriminate.
    + (* B^D *)
      injection H as E1 E2 E3 E4 E5 E6. subst. simpl in *.
      destruct IHlder1 as [_ E1]. destruct IHlder3 as [_ E3]. subst.
      intros X gm al Hg. simpl.
      destruct (IHlder2 X ((D, al) :: gm)) as [t Kt]; [simpl; rewrite Hg; reflexivity |].
      exists t. rewrite app_nil_r. exact Kt.
    + destruct r as [A0 B1 C [] | A0 a0 | A0 D B1 | G D | A0 D C B1]; simpl in Hp.
      * (* path *)
        destruct Hp as [Hp | []]. injection Hp as E1 E2 E3 E4 E5 E6. subst. simpl in *.
        destruct IHlder1 as [_ E1]. subst. simpl.
        intros X gm Hg.
        destruct (IHlder2 (SCat B1 [] :: X) gm Hg) as [t1 K1].
        destruct (IHlder3 [] [] eq_refl) as [t2 K2].
        exists (Node t1 t2). eapply d_path; [eassumption |].
        eapply derives_trans; [exact K1 |].
        rewrite <- (app_nil_r w3). eapply d_rw3; [exact K2 | apply d_refl].
      * (* def *)
        destruct Hp as [Hp | []]. injection Hp as E1 E2 E3 E4 E5 E6. subst. simpl in *.
        destruct IHlder3 as [_ E3]. subst. rewrite app_nil_r.
        intros X gm Hg.
        destruct (IHlder1 (SCat B1 gm :: X) [] eq_refl) as [t1 K1].
        destruct (IHlder2 [] gm Hg) as [t2 K2].
        exists (Node t1 t2). eapply d_def; [eassumption |].
        eapply derives_trans; [exact K1 |].
        rewrite <- (app_nil_r w2). eapply d_rw3; [exact K2 | apply d_refl].
      * (* split *)
        apply in_map_iff in Hp. destruct Hp as [D [Hp _]].
        injection Hp as E1 E2 E3 E4 E5 E6. subst. simpl in *.
        destruct IHlder1 as [_ E1]. subst. simpl.
        intros X gm Hg.
        destruct (map_fst_cons _ _ _ Hg) as [al [gm' [E Hg']]]. subst gm.
        destruct (IHlder2 (SCat B1 [(D, al)] :: X) gm' Hg') as [t1 K1].
        destruct (IHlder3 [] [] al eq_refl) as [t2 K2].
        exists (Node t1 t2). eapply d_split; [eassumption |].
        eapply derives_trans; [exact K1 |].
        rewrite <- (app_nil_r w3). eapply d_rw3; [exact K2 | apply d_refl].
      * destruct Hp as [Hp | []]; discriminate.
      * (* fronting *)
        destruct Hp as [Hp | []]. injection Hp as E1 E2 E3 E4 E5 E6. subst. simpl in *.
        destruct IHlder3 as [_ E3]. subst. rewrite app_nil_r.
        intros X gm Hg.
        destruct (IHlder1 [] [] eq_refl) as [al K1].
        destruct (IHlder2 X ((D, al) :: gm)) as [t K2]; [simpl; rewrite Hg; reflexivity |].
        exists t. eapply d_rw4; [eassumption | exact K1 | exact K2].
      * (* gap site *)
        destruct Hp as [Hp | []]. injection Hp as E1 E2 E3 E4 E5 E6. subst. simpl in *.
        destruct IHlder1 as [_ E1]. destruct IHlder2 as [E2 E2']. destruct IHlder3 as [_ E3].
        subst. simpl.
        intros X gm Hg.
        destruct (map_fst_cons _ _ _ Hg) as [al [gm' [E Hg']]]. subst gm.
        apply map_fst_nil in Hg'. subst.
        exists al. eapply d_rw6; [eassumption | apply d_refl].
      * (* LINK *)
        destruct Hp as [Hp | [Hp | []]];
          injection Hp as E1 E2 E3 E4 E5 E6; subst; simpl in *.
        -- destruct IHlder1 as [_ E1]. destruct IHlder2 as [E2 E2']. subst. simpl.
           intros X gm Hg. apply map_fst_nil in Hg. subst.
           destruct (IHlder3 eq_refl X) as [t Kt].
           exists t. eapply d_rw7; [eassumption | exact Kt].
        -- destruct IHlder3 as [_ E3]. subst. rewrite app_nil_r.
           intros Hg X. subst.
           destruct (IHlder1 (SLink D C :: X) [] eq_refl) as [t1 K1].
           destruct (IHlder2 [] [] t1 eq_refl) as [t2 K2].
           exists (Node t1 (LinkT t2)).
           eapply derives_trans; [exact K1 |].
           rewrite <- (app_nil_r w2). eapply d_rw8; [exact K2 | apply d_refl].
Qed.

(* Upper bound: a stacked-slash path grammar generates exactly the strings
   of the linear indexed grammar G-natural.  G-natural is a finite list of
   productions, so every stacked-slash language is a linear indexed
   language. *)
Theorem ssg_lig_equivalence : forall S w,
  ssg_language S w <-> lig_language S w.
Proof.
  intros S w; split.
  - intros [t H]. eapply ssg_to_lig; eauto.
  - intro H. destruct (lig_to_ssg _ _ _ H [] [] eq_refl) as [t Ht]. exists t. exact Ht.
Qed.

(* ===================================================================== *)
(*  Tree-level characterisation.                                         *)
(*                                                                       *)
(*  tder A gm w t : A with the pending fillers gm derives w, and t is    *)
(*  the term built, with each filler placed at its gap.                  *)
(* ===================================================================== *)

Inductive tder : nonterminal -> fstack -> list terminal -> term -> Prop :=
  | t_term : forall A a,
      In (TRule A a) R -> tder A [] [a] (Leaf a)
  | t_path : forall A B C g w1 w2 t1 t2,
      In (PRule A B C Path) R -> tder C g w1 t1 -> tder B [] w2 t2 ->
      tder A g (w1 ++ w2) (Node t1 t2)
  | t_def : forall A B C g w1 w2 t1 t2,
      In (PRule A B C Def) R -> tder C [] w1 t1 -> tder B g w2 t2 ->
      tder A g (w1 ++ w2) (Node t1 t2)
  | t_split : forall A B C D al g w1 w2 t1 t2,
      In (PRule A B C Split) R -> tder C g w1 t1 -> tder B [(D, al)] w2 t2 ->
      tder A ((D, al) :: g) (w1 ++ w2) (Node t1 t2)
  | t_top : forall A D B g al w1 w2 t,
      In (TopRule A D B) R -> tder D [] w1 al -> tder B ((D, al) :: g) w2 t ->
      tder A g (w1 ++ w2) t
  | t_gap : forall G D al,
      In (GapRule G D) R -> tder G [(D, al)] [] al
  | t_link : forall A D C B w1 w2 t1 t2,
      In (LRule A D C B) R -> tder B [] w1 t1 -> tder C [(D, t1)] w2 t2 ->
      tder A [] (w1 ++ w2) (Node t1 (LinkT t2)).

Lemma tder_to_ssg : forall A g w t,
  tder A g w t -> forall X, derives (X, FCat A g) w (X, FT t).
Proof.
  intros A g w t H; induction H; intros X.
  - rewrite <- (app_nil_r [a]). eapply d_rw2; [eassumption | apply d_refl].
  - eapply d_path; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [apply IHtder2 | apply d_refl].
  - eapply d_def; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [apply IHtder2 | apply d_refl].
  - eapply d_split; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw3; [apply IHtder2 | apply d_refl].
  - eapply d_rw4; [eassumption | apply IHtder1 | apply IHtder2].
  - eapply d_rw6; [eassumption | apply d_refl].
  - eapply d_rw7; [eassumption |].
    eapply derives_trans; [apply IHtder1 |].
    rewrite <- (app_nil_r w2). eapply d_rw8; [apply IHtder2 | apply d_refl].
Qed.

(* fill t X w T : attaching to t the subtrees for the stack symbols X (top
   first) yields T, and those subtrees have yield w.  A LINK site receives
   a linked tree whose gap holds a copy of the term to its left. *)
Inductive fill : term -> list ssym -> list terminal -> term -> Prop :=
  | f_nil : forall t, fill t [] [] t
  | f_cat : forall t B g X w1 w2 tB T,
      tder B g w1 tB -> fill (Node t tB) X w2 T ->
      fill t (SCat B g :: X) (w1 ++ w2) T
  | f_lk : forall t D C X w1 w2 tL T,
      tder C [(D, t)] w1 tL -> fill (Node t (LinkT tL)) X w2 T ->
      fill t (SLink D C :: X) (w1 ++ w2) T.

(* tcontent c w T : the item c can be completed, emitting w, to the final
   term T. *)
Definition tcontent (c : item) (w : list terminal) (T : term) : Prop :=
  match c with
  | (X, FT t) => fill t X w T
  | (X, FCat A g) => exists w1 w2 t, w = w1 ++ w2 /\ tder A g w1 t /\ fill t X w2 T
  end.

Lemma sub_tder : forall A g s tB,
  (forall w T, tcontent ([], FT tB) w T -> tcontent ([], FCat A g) (s ++ w) T) ->
  tder A g s tB.
Proof.
  intros A g s tB H.
  assert (Hc : tcontent ([], FCat A g) (s ++ []) tB) by (apply H; constructor).
  destruct Hc as [w1 [w2 [t [E [Ht Hf]]]]].
  inversion Hf; subst. rewrite !app_nil_r in E. subst. exact Ht.
Qed.

Lemma derives_tcontent : forall c s c',
  derives c s c' -> forall w T, tcontent c' w T -> tcontent c (s ++ w) T.
Proof.
  intros c s c' H; induction H; intros w T Hc.
  - exact Hc.
  - (* path *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_path; eauto.
    + assumption.
  - (* def *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_def; eauto.
    + assumption.
  - (* split *)
    destruct (IHderives w T Hc) as [w1 [w2 [tC [E [HC Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tC tB). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_split; eauto.
    + assumption.
  - (* RW2 *)
    exists [a], (s ++ w), (Leaf a). repeat split.
    + apply t_term; assumption.
    + apply (IHderives w T Hc).
  - (* RW3 *)
    pose proof (sub_tder _ _ _ _ IHderives1) as HB.
    simpl. rewrite <- app_assoc. eapply f_cat; [exact HB | exact (IHderives2 w T Hc)].
  - (* RW4 *)
    pose proof (sub_tder _ _ _ _ IHderives1) as HD.
    destruct (IHderives2 w T Hc) as [w1 [w2 [t [E [Ht Hf]]]]].
    exists (s1 ++ w1), w2, t. repeat split.
    + rewrite <- app_assoc, E. apply app_assoc.
    + eapply t_top; eauto.
    + assumption.
  - (* RW6 *)
    exists [], (s ++ w), al. repeat split.
    + apply t_gap; assumption.
    + apply (IHderives w T Hc).
  - (* RW7 *)
    destruct (IHderives w T Hc) as [w1 [w2 [tB [E [HB Hf]]]]].
    inversion Hf; subst.
    exists (w1 ++ w0), w3, (Node tB (LinkT tL)). repeat split.
    + rewrite E. apply app_assoc.
    + eapply t_link; eauto.
    + assumption.
  - (* RW8 *)
    pose proof (sub_tder _ _ _ _ IHderives1) as HL.
    simpl. rewrite <- app_assoc. eapply f_lk; [exact HL | exact (IHderives2 w T Hc)].
Qed.

(* The terms built by a stacked-slash path grammar are exactly those of
   the filled derivations, for every category and every filler stack. *)
Theorem ssg_tree_characterisation : forall A g w t,
  derives ([], FCat A g) w ([], FT t) <-> tder A g w t.
Proof.
  intros A g w t; split.
  - intro H. apply sub_tder. intros w' T Hc.
    exact (derives_tcontent _ _ _ H w' T Hc).
  - intro H. exact (tder_to_ssg _ _ _ _ H []).
Qed.

(* Item completion: every item of a derivation ending in T can be
   completed to T. *)
Corollary ssg_item_completion : forall c s T,
  derives c s ([], FT T) -> tcontent c s T.
Proof.
  intros c s T H. rewrite <- (app_nil_r s).
  apply (derives_tcontent _ _ _ H). constructor.
Qed.

(* Every plain category derives a non-empty string: fillers are never
   empty, and the language contains no empty string. *)
Lemma tder_nonempty : forall A g w t, tder A g w t -> g = [] -> w <> [].
Proof.
  intros A g w t H; induction H; intros Eg; try discriminate.
  - subst. intro E. apply app_eq_nil in E. destruct E as [E _]. exact (IHtder1 eq_refl E).
  - intro E. apply app_eq_nil in E. destruct E as [E _]. exact (IHtder1 eq_refl E).
  - intro E. apply app_eq_nil in E. destruct E as [E _]. exact (IHtder1 eq_refl E).
  - intro E. apply app_eq_nil in E. destruct E as [E _]. exact (IHtder1 eq_refl E).
Qed.

Corollary ssg_epsilon_free : forall S w, ssg_language S w -> w <> [].
Proof.
  intros S w [t H]. apply ssg_tree_characterisation in H.
  exact (tder_nonempty _ _ _ _ H eq_refl).
Qed.

(* ===================================================================== *)
(*  Flattened derivations and nested item completion (incrementality).   *)
(*  Frames record the enclosing step of a nested sub-derivation:        *)
(*    FrP X t       : an RW3 pop;                                        *)
(*    FrL X t       : an RW8 LINK resolution with host t;                *)
(*    FrT X B D g   : an RW4 fronting step building its filler, which    *)
(*                    will continue as B with D pushed onto g.           *)
(* ===================================================================== *)

Inductive frame : Type :=
  | FrP : list ssym -> term -> frame
  | FrL : list ssym -> term -> frame
  | FrT : list ssym -> nonterminal -> nonterminal -> fstack -> frame.

Definition config : Type := (list frame * item)%type.

Inductive mstep : config -> list terminal -> config -> Prop :=
  | m_path : forall F X A B C g, In (PRule A B C Path) R ->
      mstep (F, (X, FCat A g)) [] (F, (SCat B [] :: X, FCat C g))
  | m_def : forall F X A B C g, In (PRule A B C Def) R ->
      mstep (F, (X, FCat A g)) [] (F, (SCat B g :: X, FCat C []))
  | m_split : forall F X A B C D al g, In (PRule A B C Split) R ->
      mstep (F, (X, FCat A ((D, al) :: g))) [] (F, (SCat B [(D, al)] :: X, FCat C g))
  | m_rw2 : forall F X A a, In (TRule A a) R ->
      mstep (F, (X, FCat A [])) [a] (F, (X, FT (Leaf a)))
  | m_call3 : forall F X B g t,
      mstep (F, (SCat B g :: X, FT t)) [] (FrP X t :: F, ([], FCat B g))
  | m_ret3 : forall F X t tB,
      mstep (FrP X t :: F, ([], FT tB)) [] (F, (X, FT (Node t tB)))
  | m_call4 : forall F X A D B g, In (TopRule A D B) R ->
      mstep (F, (X, FCat A g)) [] (FrT X B D g :: F, ([], FCat D []))
  | m_ret4 : forall F X B D g al,
      mstep (FrT X B D g :: F, ([], FT al)) [] (F, (X, FCat B ((D, al) :: g)))
  | m_rw6 : forall F X G D al, In (GapRule G D) R ->
      mstep (F, (X, FCat G [(D, al)])) [] (F, (X, FT al))
  | m_rw7 : forall F X A D C B, In (LRule A D C B) R ->
      mstep (F, (X, FCat A [])) [] (F, (SLink D C :: X, FCat B []))
  | m_call8 : forall F X D C t,
      mstep (F, (SLink D C :: X, FT t)) [] (FrL X t :: F, ([], FCat C [(D, t)]))
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
  - eapply ms_one; [apply m_path; eassumption | apply IHderives].
  - eapply ms_one; [apply m_def; eassumption | apply IHderives].
  - eapply ms_one; [apply m_split; eassumption | apply IHderives].
  - change (a :: s) with ([a] ++ s). eapply ms_step; [apply m_rw2; eassumption | apply IHderives].
  - eapply ms_one; [apply m_call3 |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret3 | apply IHderives2].
  - eapply ms_one; [eapply m_call4; eassumption |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret4 | apply IHderives2].
  - eapply ms_one; [eapply m_rw6; eassumption | apply IHderives].
  - eapply ms_one; [apply m_rw7; eassumption | apply IHderives].
  - eapply ms_one; [apply m_call8 |].
    eapply msteps_trans; [apply IHderives1 |].
    eapply ms_one; [apply m_ret8 | apply IHderives2].
Qed.

Lemma tcontent_nil : forall A g s tB, tcontent ([], FCat A g) s tB -> tder A g s tB.
Proof.
  intros A g s tB [w1 [w2 [t [E [Ht Hf]]]]].
  inversion Hf; subst. rewrite app_nil_r. exact Ht.
Qed.

(* gcontent F c w T : the item c, nested inside the frames F, can be
   completed, emitting w, to the final term T. *)
Fixpoint gcontent (F : list frame) (c : item) (w : list terminal) (T : term) : Prop :=
  match F with
  | [] => tcontent c w T
  | FrP X t :: F' => exists w1 w2 tB,
      w = w1 ++ w2 /\ tcontent c w1 tB /\ gcontent F' (X, FT (Node t tB)) w2 T
  | FrL X t :: F' => exists w1 w2 tL,
      w = w1 ++ w2 /\ tcontent c w1 tL /\ gcontent F' (X, FT (Node t (LinkT tL))) w2 T
  | FrT X B D g :: F' => exists w1 w2 al,
      w = w1 ++ w2 /\ tcontent c w1 al /\ gcontent F' (X, FCat B ((D, al) :: g)) w2 T
  end.

Lemma gcontent_lift : forall c c' s,
  (forall w T, tcontent c' w T -> tcontent c (s ++ w) T) ->
  forall F w T, gcontent F c' w T -> gcontent F c (s ++ w) T.
Proof.
  intros c c' s Hl F w T. destruct F as [| [X t | X t | X B D g] F']; simpl.
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

Lemma mstep_gcontent : forall k s k',
  mstep k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; inversion H; subst; cbn [fst snd]; intros w T Hg.
  - eapply local_lift; [eapply d_path; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_def; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_split; [exact H0 | apply d_refl] | exact Hg].
  - apply (local_lift _ _ _ (d_rw2 _ _ _ _ _ H0 (d_refl _))). exact Hg.
  - simpl in Hg. destruct Hg as [w1 [w2 [tB [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' Hc'. simpl. eapply f_cat; [apply tcontent_nil; exact Hc | exact Hc'].
  - simpl. exists [], w, tB. repeat split; [constructor | exact Hg].
  - simpl in Hg. destruct Hg as [w1 [w2 [al [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' [u1 [u2 [t [E' [Ht Hf]]]]].
    exists (w1 ++ u1), u2, t. repeat split.
    + rewrite E'. apply app_assoc.
    + eapply t_top; [eassumption | apply tcontent_nil; exact Hc | exact Ht].
    + exact Hf.
  - simpl. exists [], w, al. repeat split; [constructor | exact Hg].
  - eapply local_lift; [eapply d_rw6; [exact H0 | apply d_refl] | exact Hg].
  - eapply local_lift; [eapply d_rw7; [exact H0 | apply d_refl] | exact Hg].
  - simpl in Hg. destruct Hg as [w1 [w2 [tL [E [Hc Hg]]]]]. subst. simpl.
    eapply gcontent_lift with (s := w1); [| exact Hg].
    intros w' T' Hc'. simpl. eapply f_lk; [apply tcontent_nil; exact Hc | exact Hc'].
  - simpl. exists [], w, tL. repeat split; [constructor | exact Hg].
Qed.

Lemma msteps_gcontent : forall k s k',
  msteps k s k' -> forall w T, gcontent (fst k') (snd k') w T -> gcontent (fst k) (snd k) (s ++ w) T.
Proof.
  intros k s k' H; induction H; intros w T Hg.
  - exact Hg.
  - rewrite <- app_assoc. eapply mstep_gcontent; [exact H | apply IHmsteps; exact Hg].
Qed.

(* Nested item completion: every configuration of a flattened derivation
   ending in T, including items inside the sub-derivations of RW3, RW4 and
   RW8, can be completed to T.  Pending fillers are held by the slashed
   categories that will place them, or, while under construction, by the
   fronting frame that will push them. *)
Corollary ssg_nested_item_completion : forall k s T,
  msteps k s ([], ([], FT T)) -> gcontent (fst k) (snd k) s T.
Proof.
  intros k s T H. rewrite <- (app_nil_r s).
  apply (msteps_gcontent _ _ _ H). simpl. constructor.
Qed.

Theorem ssg_machine_equivalence : forall A g w t,
  msteps ([], ([], FCat A g)) w ([], ([], FT t)) <-> derives ([], FCat A g) w ([], FT t).
Proof.
  intros A g w t; split.
  - intro H. apply ssg_tree_characterisation.
    pose proof (ssg_nested_item_completion _ _ _ H) as Hg. simpl in Hg.
    apply tcontent_nil. exact Hg.
  - intro H. exact (derives_to_machine _ _ _ H []).
Qed.

(* ===================================================================== *)
(*  Linear contexts: the term built for A/gm is a context with one hole  *)
(*  per pending filler, independent of the fillers, and each filler is   *)
(*  placed exactly once.  Hole n stands for the n-th filler, counted     *)
(*  from the top of the stack.                                           *)
(* ===================================================================== *)

Inductive ctx : Type :=
  | CHole : nat -> ctx
  | CLeaf : terminal -> ctx
  | CNode : ctx -> ctx -> ctx
  | CLink : ctx -> ctx.

Fixpoint holes (k : ctx) : list nat :=
  match k with
  | CHole n => [n]
  | CLeaf _ => []
  | CNode k1 k2 => holes k1 ++ holes k2
  | CLink k1 => holes k1
  end.

Fixpoint plug (k : ctx) (fs : list term) : option term :=
  match k with
  | CHole n => nth_error fs n
  | CLeaf a => Some (Leaf a)
  | CNode k1 k2 =>
      match plug k1 fs, plug k2 fs with
      | Some t1, Some t2 => Some (Node t1 t2)
      | _, _ => None
      end
  | CLink k1 =>
      match plug k1 fs with
      | Some t1 => Some (LinkT t1)
      | None => None
      end
  end.

Fixpoint of_term (t : term) : ctx :=
  match t with
  | ExtendedPathGrammars.Leaf a => CLeaf a
  | ExtendedPathGrammars.Node t1 t2 => CNode (of_term t1) (of_term t2)
  | ExtendedPathGrammars.LinkT t1 => CLink (of_term t1)
  end.

Fixpoint shift (k : ctx) : ctx :=
  match k with
  | CHole n => CHole (S n)
  | CLeaf a => CLeaf a
  | CNode k1 k2 => CNode (shift k1) (shift k2)
  | CLink k1 => CLink (shift k1)
  end.

(* Fill hole 0 with a fixed term and renumber the others. *)
Fixpoint close0 (k : ctx) (t : term) : ctx :=
  match k with
  | CHole 0 => of_term t
  | CHole (S n) => CHole n
  | CLeaf a => CLeaf a
  | CNode k1 k2 => CNode (close0 k1 t) (close0 k2 t)
  | CLink k1 => CLink (close0 k1 t)
  end.

Definition dec (n : nat) : list nat := match n with 0 => [] | S m => [m] end.

Lemma of_term_plug : forall t fs, plug (of_term t) fs = Some t.
Proof. induction t; intros fs; simpl; try rewrite IHt1, IHt2; try rewrite IHt; reflexivity. Qed.

Lemma of_term_holes : forall t, holes (of_term t) = [].
Proof. induction t; simpl; try rewrite IHt1, IHt2; auto. Qed.

Lemma shift_plug : forall k f fs, plug (shift k) (f :: fs) = plug k fs.
Proof. induction k; intros f fs; simpl; try rewrite IHk1, IHk2; try rewrite IHk; reflexivity. Qed.

Lemma shift_holes : forall k, holes (shift k) = map S (holes k).
Proof. induction k; simpl; try rewrite IHk1, IHk2, map_app; auto. Qed.

Lemma close0_plug : forall k t fs, plug (close0 k t) fs = plug k (t :: fs).
Proof.
  induction k as [[| n] | a | k1 IH1 k2 IH2 | k1 IH]; intros t fs; simpl;
    try rewrite IH1, IH2; try rewrite IH; try apply of_term_plug; reflexivity.
Qed.

Lemma close0_holes : forall k t, holes (close0 k t) = flat_map dec (holes k).
Proof.
  induction k as [[| n] | a | k1 IH1 k2 IH2 | k1 IH]; intros t; simpl;
    try rewrite IH1, IH2, flat_map_app; try rewrite IH; try apply of_term_holes; reflexivity.
Qed.

Lemma plug_prefix : forall k fs1 fs2,
  (forall n, In n (holes k) -> n < length fs1) -> plug k (fs1 ++ fs2) = plug k fs1.
Proof.
  induction k as [n | a | k1 IH1 k2 IH2 | k1 IH]; intros fs1 fs2 H; simpl in *.
  - apply nth_error_app1. apply H. left; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; auto; intros m Hm; apply H; apply in_or_app; auto.
  - rewrite IH; auto.
Qed.

Lemma flat_map_dec_S : forall l, flat_map dec (map S l) = l.
Proof. induction l; simpl; [| rewrite IHl]; reflexivity. Qed.

Lemma seq_S_shift : forall n, seq 0 (S n) = 0 :: map S (seq 0 n).
Proof. intros n. simpl. rewrite seq_shift. reflexivity. Qed.

Theorem linear_context : forall A g w t, tder A g w t ->
  exists k, Permutation (holes k) (seq 0 (length g)) /\
    plug k (map snd g) = Some t /\
    forall g', map fst g' = map fst g ->
      exists t', plug k (map snd g') = Some t' /\ tder A g' w t'.
Proof.
  intros A g w t H; induction H.
  - (* t_term *)
    exists (CLeaf a). repeat split; [constructor |].
    intros g' Hg. apply map_fst_nil in Hg. subst.
    exists (Leaf a). split; [reflexivity | apply t_term; assumption].
  - (* t_path *)
    destruct IHtder1 as [kC [PC [EC IC]]]. destruct IHtder2 as [kB [PB [EB IB]]].
    simpl in PB. apply Permutation_sym, Permutation_nil in PB.
    assert (HB : forall fs, plug kB fs = Some t2).
    { intros fs. rewrite <- (app_nil_l fs). rewrite plug_prefix; [exact EB |].
      rewrite PB. intros n []. }
    exists (CNode kC kB). repeat split.
    + simpl. rewrite PB, app_nil_r. exact PC.
    + simpl. rewrite EC, HB. reflexivity.
    + intros g' Hg. destruct (IC g' Hg) as [t1' [E1 K1]].
      exists (Node t1' t2). split; [simpl; rewrite E1, HB; reflexivity |].
      eapply t_path; eauto.
  - (* t_def *)
    destruct IHtder1 as [kC [PC [EC IC]]]. destruct IHtder2 as [kB [PB [EB IB]]].
    simpl in PC. apply Permutation_sym, Permutation_nil in PC.
    assert (HC : forall fs, plug kC fs = Some t1).
    { intros fs. rewrite <- (app_nil_l fs). rewrite plug_prefix; [exact EC |].
      rewrite PC. intros n []. }
    exists (CNode kC kB). repeat split.
    + simpl. rewrite PC. exact PB.
    + simpl. rewrite HC, EB. reflexivity.
    + intros g' Hg. destruct (IB g' Hg) as [t2' [E2 K2]].
      exists (Node t1 t2'). split; [simpl; rewrite HC, E2; reflexivity |].
      eapply t_def; eauto.
  - (* t_split *)
    destruct IHtder1 as [kC [PC [EC IC]]]. destruct IHtder2 as [kB [PB [EB IB]]].
    simpl in PB.
    assert (HB : forall f fs, plug kB (f :: fs) = plug kB [f]).
    { intros f fs. change (f :: fs) with ([f] ++ fs). apply plug_prefix.
      intros n Hn. apply (Permutation_in _ PB) in Hn. destruct Hn as [<- | []]. auto. }
    exists (CNode (shift kC) kB). repeat split.
    + simpl. rewrite shift_holes, <- seq_shift.
      apply Permutation_trans with (map S (holes kC) ++ [0]);
        [apply Permutation_app_head; exact PB |].
      apply Permutation_trans with (0 :: map S (holes kC));
        [apply Permutation_sym, Permutation_cons_append |].
      constructor. apply Permutation_map. exact PC.
    + simpl. rewrite shift_plug, EC, HB. simpl in EB. rewrite EB. reflexivity.
    + intros g' Hg. simpl in Hg.
      destruct (map_fst_cons _ _ _ Hg) as [al' [g0 [E Hg0]]]. subst g'.
      destruct (IC g0 Hg0) as [t1' [E1 K1]].
      destruct (IB [(D, al')] eq_refl) as [t2' [E2 K2]].
      exists (Node t1' t2'). split.
      * simpl. rewrite shift_plug, E1, HB. simpl in E2. rewrite E2. reflexivity.
      * eapply t_split; eauto.
  - (* t_top *)
    destruct IHtder2 as [kB [PB [EB IB]]].
    exists (close0 kB al). repeat split.
    + rewrite close0_holes. simpl in PB. rewrite <- seq_shift in PB.
      apply (Permutation_flat_map dec) in PB. simpl in PB.
      rewrite flat_map_dec_S in PB. exact PB.
    + rewrite close0_plug. exact EB.
    + intros g' Hg. destruct (IB ((D, al) :: g')) as [t' [E K']].
      { simpl. rewrite Hg. reflexivity. }
      exists t'. split; [rewrite close0_plug; exact E | eapply t_top; eauto].
  - (* t_gap *)
    exists (CHole 0). repeat split; [apply Permutation_refl |].
    intros g' Hg. simpl in Hg.
    destruct (map_fst_cons _ _ _ Hg) as [al' [g0 [E Hg0]]]. subst g'.
    apply map_fst_nil in Hg0. subst g0.
    exists al'. split; [reflexivity | apply t_gap; assumption].
  - (* t_link *)
    exists (of_term (Node t1 (LinkT t2))). repeat split.
    + rewrite of_term_holes. constructor.
    + apply of_term_plug.
    + intros g' Hg. apply map_fst_nil in Hg. subst.
      exists (Node t1 (LinkT t2)). split; [apply of_term_plug | eapply t_link; eauto].
Qed.

End Stacked.

(* ===================================================================== *)
(*  Extended Path Grammars are the depth-1 fragment.                     *)
(*                                                                       *)
(*  An extended path grammar over N is encoded over N x bool: (A, false) *)
(*  is A with no pending filler and (A, true) is A carrying exactly one  *)
(*  pending filler.  Primed categories have no fronting, LINK or lexical *)
(*  rules, and (D, true) is a gap site for D-fillers.  The encoding      *)
(*  preserves strings and terms.                                          *)
(* ===================================================================== *)

Section Embedding.

Variables terminal nonterminal : Type.
Variable allN : list nonterminal.
Hypothesis allN_complete : forall A : nonterminal, In A allN.
Variable ER : list (ExtendedPathGrammars.rule terminal nonterminal).

Notation term := (ExtendedPathGrammars.term terminal).
Notation Leaf := ExtendedPathGrammars.Leaf.
Notation Node := ExtendedPathGrammars.Node.
Notation LinkT := ExtendedPathGrammars.LinkT.
Notation N2 := (nonterminal * bool)%type.

Definition embed_rule (r : ExtendedPathGrammars.rule terminal nonterminal)
  : list (rule terminal N2) :=
  match r with
  | ExtendedPathGrammars.PRule _ _ A B C =>
      [PRule _ _ (A, false) (B, false) (C, false) Path;
       PRule _ _ (A, true) (B, false) (C, true) Path;
       PRule _ _ (A, true) (B, true) (C, false) Def]
  | ExtendedPathGrammars.TRule _ _ A a => [TRule _ _ (A, false) a]
  | ExtendedPathGrammars.TopRule _ _ A D => [TopRule _ _ (A, false) (D, false) (A, true)]
  | ExtendedPathGrammars.LRule _ _ A D C B =>
      [LRule _ _ (A, false) (D, false) (C, true) (B, false)]
  end.

Definition embed : list (rule terminal N2) :=
  flat_map embed_rule ER ++ map (fun D => GapRule _ _ (D, true) (D, false)) allN.

Notation etder := (ExtendedPathGrammars.tder terminal nonterminal ER).
Notation stder := (tder terminal N2 embed).

Lemma in_embed : forall r p, In r ER -> In p (embed_rule r) -> In p embed.
Proof. intros r p Hr Hp. unfold embed. apply in_or_app. left. apply in_flat_map. eauto. Qed.

Lemma in_embed_gap : forall D, In (GapRule _ _ (D, true) (D, false)) embed.
Proof.
  intros D. unfold embed. apply in_or_app. right.
  apply (in_map (fun D => GapRule terminal N2 (D, true) (D, false))). apply allN_complete.
Qed.

Lemma in_embed_inv : forall p, In p embed ->
  (exists D, p = GapRule _ _ (D, true) (D, false)) \/
  (exists r, In r ER /\ In p (embed_rule r)).
Proof.
  intros p H. unfold embed in H. apply in_app_or in H. destruct H as [H | H].
  - right. apply in_flat_map in H. exact H.
  - left. apply in_map_iff in H. destruct H as [D [E _]]. eauto.
Qed.

Lemma epg_to_embed : forall c w t, etder c w t ->
  match c with
  | ExtendedPathGrammars.TN _ _ A => stder (A, false) [] w t
  | ExtendedPathGrammars.TS _ _ A D al => stder (A, true) [((D, false), al)] w t
  end.
Proof.
  intros c w t H; induction H.
  - apply t_term. eapply in_embed; [eassumption | left; reflexivity].
  - eapply t_path; [eapply in_embed; [eassumption | left; reflexivity] | exact IHtder1 | exact IHtder2].
  - eapply t_top; [eapply in_embed; [eassumption | left; reflexivity] | exact IHtder1 | exact IHtder2].
  - eapply t_link; [eapply in_embed; [eassumption | left; reflexivity] | exact IHtder1 | exact IHtder2].
  - eapply t_def; [eapply in_embed; [eassumption | right; right; left; reflexivity]
                  | exact IHtder1 | exact IHtder2].
  - eapply t_path; [eapply in_embed; [eassumption | right; left; reflexivity]
                   | exact IHtder1 | exact IHtder2].
  - apply t_gap. apply in_embed_gap.
Qed.

Ltac rule_cases Hm :=
  apply in_embed_inv in Hm;
  let D := fresh "D" in let r := fresh "r" in let Hr := fresh "Hr" in let Hp := fresh "Hp" in
  destruct Hm as [[D Hm] | [r [Hr Hp]]];
  [try discriminate |
   destruct r; simpl in Hp;
   repeat (destruct Hp as [Hp | Hp]; [try discriminate |]); try contradiction].

Lemma embed_to_epg : forall X g w t, stder X g w t ->
  match X with
  | (A, false) => g = [] -> etder (ExtendedPathGrammars.TN _ _ A) w t
  | (A, true) => forall D al, g = [((D, false), al)] ->
      etder (ExtendedPathGrammars.TS _ _ A D al) w t
  end.
Proof.
  intros X g w t H; induction H.
  - (* t_term *)
    rename H into Hm. rule_cases Hm. injection Hp as E1 E2. subst. simpl.
    intros _. apply ExtendedPathGrammars.t_term. assumption.
  - (* t_path *)
    rename H into Hm. rule_cases Hm; injection Hp as E1 E2 E3; subst; simpl in *.
    + intros Eg. subst.
      eapply ExtendedPathGrammars.t_bin; [eassumption | apply IHtder1; reflexivity
                                          | apply IHtder2; reflexivity].
    + intros D0 al Eg. subst.
      eapply ExtendedPathGrammars.t_sb; [eassumption | apply IHtder1; reflexivity
                                         | apply IHtder2; reflexivity].
  - (* t_def *)
    rename H into Hm. rule_cases Hm. injection Hp as E1 E2 E3. subst. simpl in *.
    intros D0 al Eg. subst.
    eapply ExtendedPathGrammars.t_sa; [eassumption | apply IHtder1; reflexivity
                                       | apply IHtder2; reflexivity].
  - (* t_split: no split rules *)
    rename H into Hm. rule_cases Hm.
  - (* t_top *)
    rename H into Hm. rule_cases Hm. injection Hp as E1 E2 E3. subst. simpl in *.
    intros Eg. subst.
    eapply ExtendedPathGrammars.t_top; [eassumption | apply IHtder1; reflexivity
                                        | apply IHtder2; reflexivity].
  - (* t_gap *)
    rename H into Hm. apply in_embed_inv in Hm.
    destruct Hm as [[D0 Hm] | [r [Hr Hp]]].
    + injection Hm as E1 E2. subst. simpl.
      intros D1 al1 Eg. injection Eg as E1 E2. subst.
      apply ExtendedPathGrammars.t_gap.
    + destruct r; simpl in Hp;
        repeat (destruct Hp as [Hp | Hp]; [try discriminate |]); try contradiction.
  - (* t_link *)
    rename H into Hm. rule_cases Hm. injection Hp as E1 E2 E3 E4. subst. simpl in *.
    intros _.
    eapply ExtendedPathGrammars.t_link; [eassumption | apply IHtder1; reflexivity
                                         | apply IHtder2; reflexivity].
Qed.

(* Strings and terms are preserved, for plain and for slashed categories. *)
Theorem epg_embedding_trees : forall A w t,
  (etder (ExtendedPathGrammars.TN _ _ A) w t <-> stder (A, false) [] w t) /\
  (forall D al, etder (ExtendedPathGrammars.TS _ _ A D al) w t <->
                stder (A, true) [((D, false), al)] w t).
Proof.
  intros A w t; split; [| intros D al]; split; intro H.
  - exact (epg_to_embed _ _ _ H).
  - exact (embed_to_epg _ _ _ _ H eq_refl).
  - exact (epg_to_embed _ _ _ H).
  - exact (embed_to_epg _ _ _ _ H D al eq_refl).
Qed.

(* The same at the level of the rewrite semantics: an extended path
   grammar and its encoding have the same derivations, item for item at
   the top level, with the same strings and terms. *)
Theorem epg_embedding : forall A w t,
  ExtendedPathGrammars.derives terminal nonterminal ER
    ([], ExtendedPathGrammars.FNT _ _ A) w ([], ExtendedPathGrammars.FT _ _ t)
  <-> derives terminal N2 embed ([], FCat _ _ (A, false) []) w ([], FT _ _ t).
Proof.
  intros A w t.
  rewrite (ExtendedPathGrammars.epg_tree_characterisation _ _ ER
             (ExtendedPathGrammars.TN _ _ A)).
  rewrite ssg_tree_characterisation.
  apply (epg_embedding_trees A w t).
Qed.

Corollary epg_embedding_language : forall S w,
  ExtendedPathGrammars.epg_language terminal nonterminal ER S w <->
  ssg_language terminal N2 embed (S, false) w.
Proof.
  intros S w; split; intros [t H]; exists t; apply epg_embedding; exact H.
Qed.

End Embedding.
