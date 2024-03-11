Require Export SemanticTemplates.
Require Export Program.Tactics.

  
Ltac specialize_H :=
    match goal with
    |[x : ?A |- _] => match goal with
                            |[H : ?B x |- _] => match goal with
                                                |[H1 : forall u : {x : ?A & B x }, ?C |- _] => specialize (H1 (existT B x H))
                                                end
                      end
    end.

Ltac specialize_pair_H :=
    match goal with
    |[x : ?A |- _] => match goal with
                            |[y : ?B |- _] => match goal with
                                                |[H1 : forall u : A * B, ?C |- _] => specialize (H1 (x , y))
                                                end
                      end
    end.

Ltac specialize_simple_H :=
    match goal with
    |[x : ?A |- _] => match goal with
                      |[H1 : forall u : A, ?B |- _] => specialize (H1 x)
                      end
    end.

Ltac use_hypo := try repeat (specialize_H || specialize_pair_H || specialize_simple_H || destruct_one_ex || destruct_pairs).

Ltac apply_H :=
    match goal with
     |[H : _ |- _] => apply H; solve[info_eauto]
    end.

Ltac allelim :=
    match goal with
    | [x : ?A, H : forall x : ?A, _ |- _] => specialize (H x)
    end.

Ltac exists_H :=
    match goal with
      H : ?A |- {_ : _ & _} => exists H; solve[info_eauto]
    end.

Ltac exists_pair_H :=
    match goal with
      x1 : ?A , x2 : ?B |- {x : ?A * ?B & _} => exists (x1 , x2); solve[info_eauto]
    end.

Ltac assumption_H :=
    match goal with
    |[H : ?A |- ?A] => assumption
    end.

Ltac rewrite_H :=
    match goal with
    |[H : ?A = ?B |- _] => rewrite H
    end.

Ltac rewrite_G :=
    match goal with
    |[H : ?A = ?B |- _] => rewrite <- H
    end.

Ltac tac6 := intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); try exists_H; try apply_H.

Ltac tac1 := cbv in *; intros; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); try exists_H; try apply_H.

Ltac destruct_H' :=
  match goal with
    |[H : ?aspT  |-_] => destruct H
  end.

(* aspT  ni taiou suru tactic*)
Ltac tac2'' := intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); try destruct_H'; try exists_H; try apply_H.
  
Ltac destruct_H :=
  match goal with
    |[H : aspT ?A ?a ?B |-_] => destruct H
  end.

  (* aspT  ni taiou suru tactic*)
Ltac tac2 := intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); try destruct_H; try exists_H; try apply_H.

  (* aspT  ni taiou suru tactic*)
Ltac tac2' := intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); try repeat rewrite_G; try destruct_H; try exists_H; try apply_H; try reflexivity.

Ltac tac3 := intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H || destruct_H); try repeat (rewrite_G || exists_H || apply_H || reflexivity).

Ltac destruct_hyp :=
  repeat match goal with
  |[H1 : {x : ?A & ?B} |- _] => destruct H1; clear H1
  end.
  
Theorem exchange_lemma : forall A B C, ({u : {x : A & B x} & C (projT1 u)}) -> ({x : A & {_ : B x & C x}}).
Proof.
  tac1.
Defined.

Ltac tac4 :=
  solve [repeat (intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H || destruct_H);
         rewrite_G || exists_H || apply_H || reflexivity || destruct_hyp || simple eapply exchange_lemma || info_eauto)].

Ltac tac5 := tac4 || tac1.

Ltac tac7 :=
  solve [repeat (intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || specialize_pair_H || rewrite_H || destruct_H);
         rewrite_G || exists_H || exists_pair_H || apply_H || reflexivity || destruct_hyp || simple eapply exchange_lemma || info_eauto)].

Ltac tac8 := tac7 || tac1.


Ltac move_H :=
  match goal with
  |[H : _ |- _] => move H at top
  end.

Ltac move_H' n :=
  match n with
  | 0    => idtac
  | S ?m =>
    match goal with
    |[H : _ |- _] => move H at top; move_H' m
    end
  end.

Ltac tac1' n  := 
  match n with
  | 0 => cbv in *; intros; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); eexists; try apply_H
  | S ?m => move_H' n; cbv in *; intros; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H); eexists; try apply_H
  end.

Ltac tac4' n := 
  match n with
  | 0 => solve [repeat (intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H || destruct_H);
         rewrite_G || exists_H || apply_H || reflexivity || destruct_hyp || simple eapply exchange_lemma || info_eauto)]
  | S ?m => move_H' n; solve [repeat (intros; cbv in *; try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H || destruct_H);
         rewrite_G || exists_H || apply_H || reflexivity || destruct_hyp || simple eapply exchange_lemma || info_eauto)]
  end.

Ltac destruct_hyp' n :=
  match n with
  | 1 =>
    repeat match goal with
    | [H1 : {x : ?A & ?B} |- _] => destruct H1; clear H1
    end
  | 2 =>
    match goal with
    | [H1 : {x1 : ?A & {x2 : ?B & ?C}} |- _] => destruct H1 as [x1 [x2 H]]; clear H1
    end
  | 3 =>
    match goal with
    | [H1 : {x1 : ?A & {x2 : ?B & {x3 : ?C & ?D}}} |- _] => destruct H1 as [x1 [x2 [x3 H]]]; clear H1
    end
  | 4 =>
    match goal with
    | [H1 : {x1 : ?A & {x2 : ?B & {x3 : ?C & {x4 : ?D & ?E}}}} |- _] => destruct H1 as [x1 [x2 [x3 [x4 H]]]]; clear H1
    end
  | 5 =>
    match goal with
    | [H1 : {x1 : ?A & {x2 : ?B & {x3 : ?C & {x4 : ?D & {x5 : ?E & ?F}}}}} |- _] => destruct H1 as [x1 [x2 [x3 [x4 [x5 H]]]]]; clear H1
    end
  | 6 =>
    match goal with
    | [H1 : {x1 : ?A & {x2 : ?B & {x3 : ?C & {x4 : ?D & {x5 : ?E & {x6 : ?F & ?G}}}}}} |- _] => destruct H1 as [x1 [x2 [x3 [x4 [x5 [x6 H]]]]]]; clear H1
    end
  end.

Ltac tac_time n :=
  intro; cbv in *; destruct_hyp' n; apply_H.

Ltac tac_time' n :=
  intro; cbv in *; destruct_hyp' n; tac8.
