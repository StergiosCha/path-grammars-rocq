(* ===================================================================== *)
(*  Cross-serial dependencies with fillers placed in situ.                *)
(*                                                                       *)
(*  The stacked-slash path grammar VC generates exactly                  *)
(*    { w w' | w a non-empty string of noun phrases a, b },              *)
(*  where w' is w with each a replaced by its verb c and each b by d.    *)
(*  Every string has exactly one term, and in it the k-th noun phrase    *)
(*  is placed as the argument of the k-th verb.                          *)
(*                                                                       *)
(*  Checked with Coq 8.18:                                               *)
(*    coqc ExtendedPathGrammars.v                                        *)
(*    coqc -Q . "" StackedSlashPathGrammars.v                            *)
(*    coqc -Q . "" CrossSerial.v                                         *)
(* ===================================================================== *)

Require Import List Lia.
Import ListNotations.
Require ExtendedPathGrammars.
Require Import StackedSlashPathGrammars.

Inductive vn : Type :=
  | vS     (* the pre-verbal noun-phrase field *)
  | vVC    (* the verbal complex *)
  | vVPc | vVPd | vVc | vVd | vA | vB | vGA | vGB.
Inductive vt : Type := ta | tb | tc | td.

Notation term := (ExtendedPathGrammars.term vt).
Notation Leaf := (ExtendedPathGrammars.Leaf vt).
Notation Node := (ExtendedPathGrammars.Node vt).

Definition RVC : list (rule vt vn) :=
  [ PRule _ _ vVC vVPc vVC Split; PRule _ _ vVC vVPd vVC Split;
    PRule _ _ vVC vVc vGA Path;   PRule _ _ vVC vVd vGB Path;
    PRule _ _ vVPc vVc vGA Path;  PRule _ _ vVPd vVd vGB Path;
    TRule _ _ vA ta; TRule _ _ vB tb; TRule _ _ vVc tc; TRule _ _ vVd td;
    TopRule _ _ vS vA vS; TopRule _ _ vS vB vS;
    TopRule _ _ vS vA vVC; TopRule _ _ vS vB vVC;
    GapRule _ _ vGA vA; GapRule _ _ vGB vB ].

Notation td' := (tder vt vn RVC).

(* Noun phrases, their words, categories and verbs. *)
Inductive noun : Type := na | nb.
Definition nw (x : noun) : vt := match x with na => ta | nb => tb end.
Definition verb (x : noun) : vt := match x with na => tc | nb => td end.
Definition ncat (x : noun) : vn := match x with na => vA | nb => vB end.

Definition entry (p : noun * term) : vn * term := (ncat (fst p), snd p).
Definition vw (p : noun * term) : vt := verb (fst p).
Definition fl (x : noun) : noun * term := (x, Leaf (nw x)).

(* The term built by the verbal complex for the pending fillers xs (top
   first): a left-branching sequence of predicate-argument pairs, with the
   bottom filler first. *)
Fixpoint vcout (xs : list (noun * term)) : term :=
  match xs with
  | [] => Leaf ta
  | (x, al) :: xs' =>
      match xs' with
      | [] => Node al (Leaf (verb x))
      | _ => Node (vcout xs') (Node al (Leaf (verb x)))
      end
  end.

(* The term for the string  u u'. *)
Definition output (u : list noun) : term := vcout (rev (map fl u)).

Ltac rule_in H :=
  simpl in H; repeat (destruct H as [H | H]; [try discriminate |]); try contradiction.

Lemma map_entry_inj : forall xs ys, map entry xs = map entry ys -> xs = ys.
Proof.
  induction xs as [| [x al] xs IH]; intros [| [y bl] ys] H; try discriminate; auto.
  simpl in H. injection H as E1 E2 E3. f_equal; [| apply IH; exact E3].
  destruct x, y; try discriminate; subst; reflexivity.
Qed.

(* ------------------------------ Soundness ---------------------------- *)

Lemma vc_sound : forall X g w t, td' X g w t ->
  match X with
  | vA => g = [] /\ w = [ta] /\ t = Leaf ta
  | vB => g = [] /\ w = [tb] /\ t = Leaf tb
  | vVc => g = [] /\ w = [tc] /\ t = Leaf tc
  | vVd => g = [] /\ w = [td] /\ t = Leaf td
  | vGA => exists al, g = [(vA, al)] /\ w = [] /\ t = al
  | vGB => exists al, g = [(vB, al)] /\ w = [] /\ t = al
  | vVPc => exists al, g = [(vA, al)] /\ w = [tc] /\ t = Node al (Leaf tc)
  | vVPd => exists al, g = [(vB, al)] /\ w = [td] /\ t = Node al (Leaf td)
  | vVC => exists xs, xs <> [] /\ g = map entry xs /\
             w = map vw (rev xs) /\ t = vcout xs
  | vS => forall xs, g = map entry xs -> exists u, u <> [] /\
             w = map nw u ++ map vw (rev xs) ++ map verb u /\
             t = vcout (rev (map fl u) ++ xs)
  end.
Proof.
  intros X g w t H; induction H.
  - (* t_term *)
    rule_in H; injection H as E1 E2; subst; auto.
  - (* t_path *)
    rule_in H; injection H as E1 E2 E3; subst; simpl in *.
    + (* VC -> [Vc] GA *)
      destruct IHtder1 as [al [E1 [E2 E3]]]. destruct IHtder2 as [E4 [E5 E6]]. subst.
      exists [(na, al)]. repeat split; try discriminate; reflexivity.
    + (* VC -> [Vd] GB *)
      destruct IHtder1 as [al [E1 [E2 E3]]]. destruct IHtder2 as [E4 [E5 E6]]. subst.
      exists [(nb, al)]. repeat split; try discriminate; reflexivity.
    + destruct IHtder1 as [al [E1 [E2 E3]]]. destruct IHtder2 as [E4 [E5 E6]]. subst.
      exists al. auto.
    + destruct IHtder1 as [al [E1 [E2 E3]]]. destruct IHtder2 as [E4 [E5 E6]]. subst.
      exists al. auto.
  - (* t_def: none *)
    rule_in H.
  - (* t_split *)
    rule_in H; injection H as E1 E2 E3; subst; simpl in *.
    + destruct IHtder1 as [xs [Hne [Eg [Ew Et]]]].
      destruct IHtder2 as [al' [E1 [E2 E3]]]. injection E1 as E1 E1'. subst D. subst al'. subst w2 t2.
      exists ((na, al) :: xs). repeat split; try discriminate; simpl; subst;
        rewrite ?map_app; try reflexivity.
      destruct xs; [contradiction | reflexivity].
    + destruct IHtder1 as [xs [Hne [Eg [Ew Et]]]].
      destruct IHtder2 as [al' [E1 [E2 E3]]]. injection E1 as E1 E1'. subst D. subst al'. subst w2 t2.
      exists ((nb, al) :: xs). repeat split; try discriminate; simpl; subst;
        rewrite ?map_app; try reflexivity.
      destruct xs; [contradiction | reflexivity].
  - (* t_top *)
    rule_in H; injection H as E1 E2 E3; subst; simpl in *;
      destruct IHtder1 as [E1 [E2 E3]]; subst; intros xs Eg; subst.
    + (* S -> A, continue in S *)
      destruct (IHtder2 (fl na :: xs) eq_refl) as [u [Hne [Ew Et]]].
      exists (na :: u). split; [discriminate |]. split.
      * rewrite Ew. simpl. rewrite map_app, <- !app_assoc. reflexivity.
      * rewrite Et. simpl. rewrite <- app_assoc. reflexivity.
    + destruct (IHtder2 (fl nb :: xs) eq_refl) as [u [Hne [Ew Et]]].
      exists (nb :: u). split; [discriminate |]. split.
      * rewrite Ew. simpl. rewrite map_app, <- !app_assoc. reflexivity.
      * rewrite Et. simpl. rewrite <- app_assoc. reflexivity.
    + (* S -> A, continue in the verbal complex *)
      destruct IHtder2 as [ys [Hne [Eg [Ew Et]]]].
      change ((vA, Leaf ta) :: map entry xs) with (map entry (fl na :: xs)) in Eg.
      apply map_entry_inj in Eg. subst.
      exists [na]. split; [discriminate |]. split; [| reflexivity].
      simpl. rewrite map_app. reflexivity.
    + destruct IHtder2 as [ys [Hne [Eg [Ew Et]]]].
      change ((vB, Leaf tb) :: map entry xs) with (map entry (fl nb :: xs)) in Eg.
      apply map_entry_inj in Eg. subst.
      exists [nb]. split; [discriminate |]. split; [| reflexivity].
      simpl. rewrite map_app. reflexivity.
  - (* t_gap *)
    rule_in H; injection H as E1 E2; subst; eauto.
  - (* t_link: none *)
    rule_in H.
Qed.

(* ----------------------------- Completeness -------------------------- *)

Lemma vc_complete : forall xs, xs <> [] ->
  td' vVC (map entry xs) (map vw (rev xs)) (vcout xs).
Proof.
  induction xs as [| [x al] xs IH]; intros Hne; [contradiction |].
  destruct xs as [| p xs'].
  - destruct x.
    + change (td' vVC [(vA, al)] ([] ++ [tc]) (Node al (Leaf tc))).
      eapply t_path with (B := vVc) (C := vGA); [simpl; tauto | apply t_gap; simpl; tauto | apply t_term; simpl; tauto].
    + change (td' vVC [(vB, al)] ([] ++ [td]) (Node al (Leaf td))).
      eapply t_path with (B := vVd) (C := vGB); [simpl; tauto | apply t_gap; simpl; tauto | apply t_term; simpl; tauto].
  - assert (Hn : p :: xs' <> []) by discriminate.
    specialize (IH Hn).
    change (vcout ((x, al) :: p :: xs')) with (Node (vcout (p :: xs')) (Node al (Leaf (verb x)))).
    change (map vw (rev ((x, al) :: p :: xs'))) with (map vw (rev (p :: xs') ++ [(x, al)])).
    rewrite map_app. destruct x.
    + change (td' vVC ((vA, al) :: map entry (p :: xs'))
                 (map vw (rev (p :: xs')) ++ [tc])
                 (Node (vcout (p :: xs')) (Node al (Leaf tc)))).
      eapply t_split with (B := vVPc) (C := vVC); [simpl; tauto | exact IH |].
      change (td' vVPc [(vA, al)] ([] ++ [tc]) (Node al (Leaf tc))).
      eapply t_path with (B := vVc) (C := vGA); [simpl; tauto | apply t_gap; simpl; tauto | apply t_term; simpl; tauto].
    + change (td' vVC ((vB, al) :: map entry (p :: xs'))
                 (map vw (rev (p :: xs')) ++ [td])
                 (Node (vcout (p :: xs')) (Node al (Leaf td)))).
      eapply t_split with (B := vVPd) (C := vVC); [simpl; tauto | exact IH |].
      change (td' vVPd [(vB, al)] ([] ++ [td]) (Node al (Leaf td))).
      eapply t_path with (B := vVd) (C := vGB); [simpl; tauto | apply t_gap; simpl; tauto | apply t_term; simpl; tauto].
Qed.

Lemma top_in : forall x B, B = vS \/ B = vVC -> In (TopRule _ _ vS (ncat x) B) RVC.
Proof. intros [] B [-> | ->]; simpl; tauto. Qed.

Lemma noun_der : forall x, td' (ncat x) [] [nw x] (Leaf (nw x)).
Proof. intros []; apply t_term; simpl; tauto. Qed.

Lemma s_complete : forall u xs, u <> [] ->
  td' vS (map entry xs) (map nw u ++ map vw (rev xs) ++ map verb u)
      (vcout (rev (map fl u) ++ xs)).
Proof.
  induction u as [| x u IH]; intros xs Hne; [contradiction |].
  destruct u as [| y u'].
  - pose proof (vc_complete (fl x :: xs) ltac:(discriminate)) as Hc.
    replace (map nw [x] ++ map vw (rev xs) ++ map verb [x])
      with ([nw x] ++ map vw (rev (fl x :: xs))) by (simpl; rewrite map_app; reflexivity).
    replace (vcout (rev (map fl [x]) ++ xs)) with (vcout (fl x :: xs)) by reflexivity.
    apply (t_top _ _ _ vS (ncat x) vVC (map entry xs) (Leaf (nw x)));
      [apply top_in; right; reflexivity | apply noun_der | exact Hc].
  - pose proof (IH (fl x :: xs) ltac:(discriminate)) as Hs.
    replace (map nw (x :: y :: u') ++ map vw (rev xs) ++ map verb (x :: y :: u'))
      with ([nw x] ++ (map nw (y :: u') ++ map vw (rev (fl x :: xs)) ++ map verb (y :: u')))
      by (simpl; rewrite map_app, <- !app_assoc; reflexivity).
    replace (vcout (rev (map fl (x :: y :: u')) ++ xs))
      with (vcout (rev (map fl (y :: u')) ++ fl x :: xs))
      by (simpl; rewrite <- !app_assoc; reflexivity).
    apply (t_top _ _ _ vS (ncat x) vS (map entry xs) (Leaf (nw x)));
      [apply top_in; left; reflexivity | apply noun_der | exact Hs].
Qed.

(* ----------------------------- Main results -------------------------- *)

Lemma app_eq_len : forall (A : Type) (l1 l2 l3 l4 : list A),
  length l1 = length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3.
Proof.
  intros A l1; induction l1 as [| x l1 IH]; intros l2 [| y l3] l4 Hl He; try discriminate;
    auto.
  simpl in *. injection He as E1 E2. subst. f_equal. eapply IH; eauto.
Qed.

Lemma map_nw_inj : forall u v, map nw u = map nw v -> u = v.
Proof.
  induction u as [| x u IH]; intros [| y v] H; try discriminate; auto.
  simpl in H. injection H as E1 E2. f_equal; [destruct x, y; try discriminate; auto | auto].
Qed.

(* The language of VC is exactly the set of strings  u u'. *)
Lemma s_complete0 : forall u, u <> [] ->
  td' vS [] (map nw u ++ map verb u) (output u).
Proof.
  intros u Hne. pose proof (s_complete u [] Hne) as H.
  simpl in H. rewrite app_nil_r in H. exact H.
Qed.

Theorem vc_language : forall w,
  ssg_language vt vn RVC vS w <-> exists u, u <> [] /\ w = map nw u ++ map verb u.
Proof.
  intros w; split.
  - intros [t H]. apply ssg_tree_characterisation in H.
    destruct (vc_sound _ _ _ _ H [] eq_refl) as [u [Hne [Ew _]]].
    exists u. split; [exact Hne | exact Ew].
  - intros [u [Hne Ew]]. subst. exists (output u).
    apply ssg_tree_characterisation.
    exact (s_complete0 u Hne).
Qed.

(* Each string u u' has exactly one term, output u. *)
Theorem vc_unique_term : forall u t, u <> [] ->
  (derives vt vn RVC ([], FCat _ _ vS []) (map nw u ++ map verb u) ([], FT _ _ t)
   <-> t = output u).
Proof.
  intros u t Hne; split.
  - intro H. apply ssg_tree_characterisation in H.
    destruct (vc_sound _ _ _ _ H [] eq_refl) as [v [Hnv [Ew Et]]].
    simpl in Ew. rewrite app_nil_r in Et.
    assert (Hl : length u = length v).
    { apply (f_equal (@length vt)) in Ew. rewrite !app_length, !map_length in Ew.
      lia. }
    assert (Huv : u = v).
    { apply map_nw_inj. eapply app_eq_len; [rewrite !map_length; exact Hl | exact Ew]. }
    subst. reflexivity.
  - intro E. subst. apply ssg_tree_characterisation. exact (s_complete0 u Hne).
Qed.

(* Alignment: the term is the left-branching sequence of predicate-argument
   pairs, one for each noun phrase in the order heard, each pairing the
   noun phrase with its own verb.  So the k-th noun phrase is the argument
   of the k-th verb, and the dependencies cross. *)
Theorem vc_alignment_single : forall x,
  output [x] = Node (Leaf (nw x)) (Leaf (verb x)).
Proof. reflexivity. Qed.

Theorem vc_alignment : forall u x, u <> [] ->
  output (u ++ [x]) = Node (output u) (Node (Leaf (nw x)) (Leaf (verb x))).
Proof.
  intros u x Hne. unfold output. rewrite map_app, rev_app_distr. simpl.
  destruct (rev (map fl u)) eqn:E.
  - apply (f_equal (@rev _)) in E. rewrite rev_involutive in E. simpl in E.
    destruct u; [contradiction | discriminate].
  - reflexivity.
Qed.

(* ------------------- Crossing for arbitrary fillers ------------------ *)

(* The verbal complex pairs each pending filler with its own verb, for
   arbitrary filler terms: fillers of the same case are never swapped.
   fs lists the pending fillers in the order heard (bottom of the stack
   first); the stack itself lists them top first, i.e. rev fs. *)
Definition pairs (fs : list (noun * term)) : term := vcout (rev fs).

Lemma pairs_single : forall x al, pairs [(x, al)] = Node al (Leaf (verb x)).
Proof. reflexivity. Qed.

Lemma pairs_snoc : forall fs x al, fs <> [] ->
  pairs (fs ++ [(x, al)]) = Node (pairs fs) (Node al (Leaf (verb x))).
Proof.
  intros fs x al Hne. unfold pairs. rewrite rev_app_distr. simpl.
  destruct (rev fs) eqn:E.
  - apply (f_equal (@rev _)) in E. rewrite rev_involutive in E. subst. contradiction.
  - reflexivity.
Qed.

Theorem vc_crossing_fillers : forall fs w t, fs <> [] ->
  (td' vVC (map entry (rev fs)) w t <-> w = map vw fs /\ t = pairs fs).
Proof.
  intros fs w t Hne; split.
  - intro H. destruct (vc_sound _ _ _ _ H) as [xs [_ [Eg [Ew Et]]]].
    apply map_entry_inj in Eg. rewrite <- Eg in Ew, Et.
    rewrite rev_involutive in Ew. split; [exact Ew | exact Et].
  - intros [Ew Et]. subst.
    pose proof (vc_complete (rev fs)) as H. rewrite rev_involutive in H.
    apply H. intro E. apply (f_equal (@rev _)) in E. rewrite rev_involutive in E.
    contradiction.
Qed.
