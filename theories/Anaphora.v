Set Printing Goal Names.

Require Import DTSTactics.


(* anaphora resolution using the refine tactic of Coq *)

Parameters male man enter whistle surprise boy present farmer father donkey woman car motor: entity -> Type.
Parameters open receive own beat check buy praise have : entity -> entity -> Type.

Section AnaphoraResolution.

  Theorem AManHe : Type.  (* A man entered. He whistled. *)
  Proof.
    simple refine {u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1)))}.
    tac5.
  Defined.

  Print AManHe.

  Theorem inference1 : AManHe -> a_nom man whistle.
  Proof.
    tac5. 
  Defined.

  Theorem AManHeInference : resolution_record.
  Proof.
    simple refine (existT _ ({u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1)))} -> a_nom man whistle) _).
    tac5.
    simpl.
    tac5.
  Qed.

  Print AManHeInference.

  
  Variable john : entity.
  Hypothesis JohnIsABoy : boy john.

  (* Every boy will receive a present. (John is a boy.) John will open it. *)
  Definition EveryBoyJohnOpen : Type.
  Proof.
    Eval cbv in (prog_conj (every_nom boy (a_acc present receive)) (aspT {z : entity & present z} ?[asp] (open john (projT1 ?asp)))).
    simple refine {s
       : forall u : {x : entity & boy x},
         {y : entity & {_ : present y & receive y (let (a, _) := u in a)}} &
           aspT {z : entity & present z} ?[asp] (open john (let (a, _) := ?asp in a))}.
    tac5. (* tac1. tac3. tac2'. *)
  Defined.

  Print EveryBoyJohnOpen.


  (* A man entered. The man didn't whistle. *)
  Theorem AManTheManNot : Type.
  Proof.
    simple refine {u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1) -> False))}.
    tac5.
  Defined.

  Theorem inference2 : AManTheManNot -> {x : entity & {_ : man x & whistle x -> False}}.
  Proof.
    tac5.
  Defined.

  Print inference2.

  Theorem TheManNotInference : resolution_record.
  Proof.
    simple refine (existT _
                     ({u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1) -> False))} -> {x : entity & {_ : man x & whistle x -> False}})
                     _); tac5.
  Defined.
  

  (* A man entered. If the man whistles, John will be surprised. *)
  Theorem AManJohnSurprise : Type.
  Proof.
    simple refine {u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1) -> surprise john))}.
    tac5.
  Defined.

  Theorem inference3 : AManJohnSurprise -> {x : entity & {_ : man x & whistle x -> surprise john}}.
  Proof.
    tac5.
  Defined.

  Print inference3.

  Theorem JohnSurpriseInference1 : resolution_record.
  Proof.
    simple refine (existT _
                     ({u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1) -> surprise john))} -> {x : entity & {_ : man x & whistle x -> surprise john}})
                     _); tac5.
  Defined.

  Theorem inference3' : AManJohnSurprise -> ((surprise john) -> False) -> {x : entity & {_ : man x & whistle x -> False}}.
  Proof.
    tac5.
  Defined.

  Print inference3'.

  Theorem JohnSurpriseInference2 : resolution_record.
  Proof.
    simple refine (existT _
                     ({u : {x : entity & {_ : man x & enter x}} & (aspT {x : entity & man x} ?[asp1] (whistle (projT1 ?asp1) -> surprise john))} -> ((surprise john) -> False) -> {x : entity & {_ : man x & whistle x -> False}})
                     _); tac5.
  Defined.


  (* If every boy receives a^1 present, some boy will open it_1. *)
  Theorem EveryBoySomeBoy : Type.
  Proof.
    simple refine (forall w : (forall u : {x : entity & boy x}, {x : entity & {_ : present x & receive x (projT1 u)}}), {x : entity & {v : boy x & aspT {x : entity & present x} ?[asp] (open (projT1 ?asp) x)}}).
    tac5. (* tac1. tac3. tac2'. *)
  Defined.


  Hypothesis JohnIsAMan : man john.
  Hypothesis CarMotor : forall u : {x : entity & car x}, {y : entity & {_ : motor y & have y (projT1 u)}}.

  (* (Every car has a motor.) John bought a car. He checked the motor. *)
  Theorem JohnMotor : Type.
  Proof.
    simple refine {s :
           {y : entity & {_ : car y & buy y john}} &
             aspT {x : entity & man x} ?[asp1]
               (aspT {y : entity & motor y} ?[asp2]
                  (check (projT1 ?asp2) (projT1 ?asp1)))}; tac1.
    destruct CarMotor as [y0 [H3 H4]].
    exact (existT motor y0 H3).
  Defined.

  Print JohnMotor.

  Theorem inference4 : JohnMotor -> a_acc motor check john.
  Proof.
    intro.
    cbv in *.
    destruct X as [[y [H1 H2]] H3].
    destruct H3.
    destruct a.
    assert ({u : {y0 : entity & motor y0} & check (projT1 u) john} -> {y0 : entity & {_ : motor y0 & check y0 john}}).
    intro; destruct X as [[y0 X4] X5]; exists y0; exists X4; assumption.
    apply X.
    exists (let (y0, s) := CarMotor (existT car y H1) in let (H3, _) := s in existT motor y0 H3).
    assumption.
  Defined.

  Theorem JohnMotorInference1 : resolution_record.
  Proof.
    simple refine (existT _ ({s :
           {y : entity & {_ : car y & buy y john}} &
             aspT {x : entity & man x} ?[asp1]
               (aspT {y : entity & motor y} ?[asp2]
                  (check (projT1 ?asp2) (projT1 ?asp1)))} -> a_acc motor check john) _).
    tac1.
    destruct s as [y [H1 H2]].
    specialize (CarMotor (existT car y H1)).
    destruct CarMotor as [y0 [H3 H4]].
    exact (existT motor y0 H3).
    simpl.
    intro.
    cbv in *.
    destruct X as [[y [H1 H2]] H3].
    destruct H3.
    destruct a.
    assert ({u : {y0 : entity & motor y0} & check (projT1 u) john} -> {y0 : entity & {_ : motor y0 & check y0 john}}).
    intro; destruct X as [[y0 X4] X5]; exists y0; exists X4; assumption.
    simple eapply X.
    exists (let (y0, s) := CarMotor (existT car y H1) in let (H3, _) := s in existT motor y0 H3).
    assumption.
  Qed. 

  Print JohnMotorInference1.

  Theorem JohnMotorInference2 : resolution_record.
  Proof.
    simple refine (existT _ ({s :
           {y : entity & {_ : car y & buy y john}} &
             aspT {x : entity & man x} ?[asp1]
               (aspT {y : entity & motor y} ?[asp2]
                  (check (projT1 ?asp2) (projT1 ?asp1)))} -> a_acc motor check john) _); tac5.
  Defined.

  Print JohnMotorInference2.

End AnaphoraResolution.
