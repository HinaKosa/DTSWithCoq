Set Printing Goal Names.

Require Import DTSTactics.


(* anaphora resolution for several sentences from the following collection of Winograd schemas:

   [1] https://cs.nyu.edu/~davise/papers/WinogradSchemas/WSCollection.xml

   We made a minor adaptation of the sentences to our setting *)

Section Trophy.

  Variables john mary : entity.
  Variables trophy suitcase human: entity -> Type.
  Variables brown1 : entity -> Type.

  Definition brown2 : forall (n : entity -> Type)(x : entity), Type :=  fun n x => {_: n x & brown1 x}.

  Definition not_human : entity -> Prop :=
    fun x => human x -> False.

  Definition because : Type -> Type -> Type :=
  fun p q => p -> q.

  Definition because2 : Prop -> Type -> Type :=
  fun p q => p -> q.

  Variables fit_in : entity -> entity -> Type.

  Definition not_fit_in : entity -> entity -> Type :=
    fun p q => fit_in p q -> False.

  Variables  is_bigger_than : entity -> entity-> Type.

  Definition is_smaller_than : entity -> entity -> Type  :=
    fun p q => is_bigger_than q p.

  Definition anything : forall n v : entity -> Type, Type :=
    fun n v => forall u : {x : entity & n x}, v (projT1 u).

  Hypothesis TrophyNotHuman :  forall x:entity, trophy x -> (human x -> False).
  Hypothesis SuitcaseNotHuman : forall x:entity, suitcase x -> (human x -> False).
  Hypothesis AnythingSmaller : forall u: {x: entity & {y:entity & {_: suitcase y & is_smaller_than y x}}}, 
    {y:entity & {_: suitcase y & fit_in y (projT1 u)}}.
  Hypothesis AnythingBigger : forall u: {x: entity & {y:entity & {_: suitcase y & is_bigger_than y x}}}, 
    {y:entity & {_: suitcase y & (fit_in y (projT1 u) -> False)}}.


  (* A trophy doesn't fit into a brown suitcase because it is smaller than that. Cf. #4 of [1] *)

  Variable asp_it : {x : entity & human x -> False}.
  Variable asp_that : {x : entity & human x -> False}.

  Definition SuitcaseSmall : Type.
  Proof.
    Eval cbv in {_ : a_nom trophy (a_acc (brown2 suitcase) not_fit_in) & is_smaller_than (projT1 (asp_that)) (projT1 (asp_it))}.
    clear asp_it asp_that.
    simple refine {_
       : {x : entity &
         {_ : trophy x & {y : entity & {_ : {_ : suitcase y & brown1 y} & fit_in y x -> False}}}} &
           is_bigger_than (let (a, _) := (?[asp1] : {x : entity & human x -> False}) in a) (let (a, _) := (?[asp2] : {x : entity & human x -> False}) in a)}.
    destruct s as [x [X1 [y [[X2 X3] X4]]]].
    exists y.
    apply SuitcaseNotHuman.
    assumption.
    destruct s as [x [X1 [y [[X2 X3] X4]]]].
    exists x.
    apply TrophyNotHuman.
    assumption.
  Defined.

  Print SuitcaseSmall.
  
  Variable asp_the : forall (n : entity -> Type), {x : entity & n x}.

  Definition the_nom : forall (n v : entity -> Type), Type :=
    fun n v => aspT {x : entity & n x} (asp_the n) (v (projT1 (asp_the n))).

  Definition the_acc : forall (n : entity -> Type) (v : entity -> entity -> Type) (x : entity), Type :=
    fun n v x => aspT {x : entity & n x} (asp_the n) (v (projT1 (asp_the n)) x).

  
  (* A brown suitcase is smaller than a trophy, and the trophy doesn't fit into the suitcase. *)
  Definition VerifyingSuitcase : Type.
  Proof.
    Eval cbv in {_ : a_nom (brown2 suitcase) (a_acc trophy is_smaller_than) & the_nom trophy (the_acc suitcase not_fit_in)}.
    clear asp_it asp_that asp_the.
    simple refine {s
       : {x : entity &
         {_ : {_ : suitcase x & brown1 x} & {y : entity & {_ : trophy y & is_bigger_than x y}}}} &
       aspT {x : entity & trophy x} (?[asp1] : {x : entity & trophy x})
         (aspT {x : entity & suitcase x} (?[asp2] : {x : entity & suitcase x})
            (fit_in (let (a, _) := ?asp2  in a) (let (a, _) := ?asp1 in a) ->
             False))}.
    tac1.
    tac1.
  Defined.

  (* A trophy doesn't fit into a brown suitcase because it is smaller than that. ->

     A brown suitcase is smaller than a trophy, and the trophy doesn't fit into the suitcase. *)
  Theorem Inference1 : SuitcaseSmall -> VerifyingSuitcase.
  Proof.
    clear asp_it asp_that asp_the.
    tac1.
    eexists.
    Unshelve.        
    2 : {
      tac1. }
    tac1.
    exact (resolve _ _ _ (resolve _ _ _ X4)).
  Defined.
        
End Trophy.


Section Although.

  Variables pete martin : entity.
  Variable successful man : entity -> Type.
  Variable envy : entity -> entity -> Type.

  Hypothesis PeteMan : man pete.
  Hypothesis MartinMan : man martin.

  (* Pete envies Martin although he is very successful. Cf. #39 of [1] *)

  Variable asp_he : {x : entity & man x}.
  
  Theorem PeteMartin : Type.
  Proof.
    Eval cbv in {_ : envy martin pete & aspT {x:entity & man x} asp_he (successful (projT1 asp_he))}.
    clear asp_he.
    simple refine {s : envy martin pete &
                         aspT {x : entity & man x} ?[asp] (successful (let (a, _) := ?asp in a))}.
    exists pete.
    exact PeteMan.
  Defined.

  Hypothesis DoNotEnvy : forall x y : entity, successful x -> envy y x -> False.

  Theorem PeteFalse : PeteMartin -> False.
  Proof.
    clear asp_he.
    tac5.
  Defined.
    
End Although.


Section But.

  Variable sid mark : entity.
  Variable convince of: entity -> entity -> Type.
  Definition not_convince : forall x y : entity, Type :=
  fun x y => convince x y -> False.
  Variable theory male man: entity -> Type.
  Variable explain : entity -> entity -> Type.
  Variable explain' : entity -> entity -> entity -> Type.
  Definition explain_to : forall x y n:entity, Type :=
  fun x y n => {_ : explain' x n y & explain x y}.
  Variable asp_his1 : {x : entity & male x}.
  Variable asp_his2 : forall (n : entity -> Type), {y : entity & {_ : n y & of y (projT1 asp_his1)}}.
  Definition his_obj' : forall (n : entity -> Type), (entity -> entity -> Type) -> entity -> Type :=
  fun n p x => aspT {x : entity & male x} asp_his1 (aspT {y : entity & {_ : n y & of y (projT1 asp_his1)}} (asp_his2 n) (p x (projT1 (asp_his2 n)))).
  Definition his_subj' : forall n : entity -> Type, (entity -> Type) -> Type :=
    fun n p => aspT {x : entity & male x} asp_his1 (aspT {y : entity & {_ : n y & of y (projT1 asp_his1)}} (asp_his2 n) (p (projT1 (asp_his2 n)))).
    
  (* Sid explained his theory to Mark but he couldn't convince him. Cf. #47 of [1] *)
  Variable asp_he : {x : entity & man x}.
  Hypothesis ManSid: man sid.
  Hypothesis ManMark : man mark.
  Theorem SidMark : Type.
  Proof.
    Eval cbv in {_ : his_obj' theory (explain_to mark) sid & 
    not_convince (projT1 (?[asp1] {x:entity & man x}))(projT1 ?[asp2] {x:entity & man x})}.
    clear asp_he.
    simple refine {H
       : aspT {x : entity & male x} asp_his1
           (aspT
              {y : entity &
              {_ : theory y & of y (let (a, _) := asp_his1 in a)}}
              (asp_his2 theory)
              (explain_to mark sid (let (a, _) := asp_his2 theory in a))) &
        aspT {x : entity & man x} ?[asp1] (aspT {x : entity & man x} ?[asp2] 
        (not_convince (let (a, _) := ?asp1 in a) (let (a, _) := ?asp2 in a)))}.
    tac1' 1. (*mark*)
    tac1' 2. (*sid*)
  Defined.
  
  Print SidMark.
  
  Hypothesis ConvinceExplain : forall x y : entity, explain y x -> ((convince y x -> False) -> False).
  
  Theorem SidFalse : SidMark -> False.
  Proof.
    tac5.
  Qed.

End But.


Require Import QArith.

(* The definitions of time, endtime, precede, include are taken from

   [2] 宇津木舞香，戸次大介．依存型意味論による日本語のテンス・アスペクトの分析に向けて．2015年度人工知能学会全国大会（第29回）論文集．2015. *)

Definition time : Type := Q * Q.

Definition endtime : time -> Q := fun t => fst t + snd t.

Definition precede (t1 t2 : time) : Type :=
  endtime t1 < fst t2.

Definition include (t1 t2 : time) : Type :=
  fst t1 < fst t2 * snd t1 < snd t2.

Opaque Qlt endtime.

Notation "A && B" := (prog_conj A B).

(* The definitions of when, before, after are inspired by those of

   [3] Coq semantics for the GF FraCas suite. https://github.com/GU-CLASP/FraCoq/tree/iwcs2021 *)

Section When.
  
  (* I stuck a pin through a carrot. When I pulled the pin out, it left a hole. Cf. #193 of [1] *)
  
  Variable i : entity.
  Variables carrot hole human pin : entity -> Type.

  Variables pull_out leave have : time -> entity -> entity -> Type.
  Variable stick_through : time -> entity -> entity -> entity -> Type.

  Definition when (A B : time -> Type) : Type :=
    {t1 : time & {t2 : time & {s : A t1 & B t2 && (endtime t1 = endtime t2)}}}.

  Hypothesis CarrotNotHuman : forall x, carrot x -> human x -> False.
  Hypothesis PinNotHuman : forall x, pin x -> human x -> False.
  Hypothesis HoleNotHuman : forall x, hole x -> human x -> False.

  Variable asp_pin asp_it : {x : entity & human x -> False}.

  Theorem PinCarrot : Type.
  Proof.
    Eval cbv in {t1 : time &
                {s0 : a_acc pin (fun x z => a_acc carrot (stick_through t1 x) z) i &
                when (fun t => aspT {x : entity & human x -> False} asp_pin (pull_out t (projT1 asp_pin) i && precede t1 t))
                     (fun t => aspT {x : entity & human x -> False} asp_it ({x : entity & hole x && leave t x (projT1 asp_it)}))}}.
    clear asp_pin asp_it.
    simple refine {t1 : Q * Q &
                  {s1 : {y : entity & {_ : pin y & {y0 : entity & {_ : carrot y0 & stick_through t1 y y0 i}}}} &
                  {t2 : Q * Q &
                  {t3 : Q * Q &
                  {s2
                  : aspT {x : entity & human x -> False} ?[asp1]
                  {s3 : pull_out t2 (let (a, _) := ?asp1 in a) i & precede t1 t2} &
                  {s4
                  : aspT {x : entity & human x -> False} ?[asp2]
                  {x : entity & {_ : hole x & leave t3 x (let (a, _) := ?asp2 in a)}} &
                      endtime t2 = endtime t3}}}}}}.
    tac1' 4%nat.
    tac1' 4%nat.
  Defined.

  Print PinCarrot.

  Hypothesis StickThrough1 : forall t1 t2 t3 : time, forall x y : entity,
      stick_through t1 x y i -> precede t1 t2 ->
      pull_out t2 x i -> endtime t2 = endtime t3 ->
      {z : entity & hole z && leave t3 z y} -> False.

  (* it => a carrot *)
  Theorem PinCarrot' : Type.
  Proof.
    Eval cbv in {t1 : time &
                {s0 : a_acc pin (fun x z => a_acc carrot (stick_through t1 x) z) i &
                when (fun t => aspT {x : entity & human x -> False} asp_pin (pull_out t (projT1 asp_pin) i && precede t1 t))
                     (fun t => aspT {x : entity & human x -> False} asp_it ({x : entity & hole x && leave t x (projT1 asp_it)}))}}.
    clear asp_pin asp_it.
    simple refine {t1 : Q * Q &
                  {s0 : {y : entity & {_ : pin y & {y0 : entity & {_ : carrot y0 & stick_through t1 y y0 i}}}} &
                  {t2 : Q * Q &
                  {t3 : Q * Q &
                  {s1
                  : aspT {x : entity & human x -> False} ?[asp1]
                  {s2 : pull_out t2 (let (a, _) := ?asp1 in a) i & endtime t1 < (let (x, _) := t2 in x)} &
                  {s3
                  : aspT {x : entity & human x -> False} ?[asp2]
                  {x : entity & {_ : hole x & leave t3 x (let (a, _) := ?asp2 in a)}} &
                      endtime t2 = endtime t3}}}}}}.
    tac1' 4%nat.
    destruct s0 as [y [H1 [y0 [H2 H3]]]].
    exists y0.
    apply CarrotNotHuman.
    assumption.
  Defined.

  Print PinCarrot'.

  Theorem Contra1 : PinCarrot' -> False.
  Proof.
    clear asp_pin asp_it.
    tac5.
    specialize (StickThrough1 (q3, q4) (q1, q2) (q, q0) X0 X7).
    apply StickThrough1; try assumption.
    destruct X3.
    destruct s; assumption.
    destruct X3.
    destruct s; assumption.
    destruct X4; assumption.
  Defined.

  Hypothesis axiom1 : forall (t1 : time) (x : entity),
      {z : entity & {_ : hole z & have t1 z x}} ->
        {t2 : time & {y : entity & {_ : pin y &
          {_ : stick_through t2 y x i & precede t2 t1}}}}.

  Theorem ItHadAHole : Type.
  Proof.
    Eval cbv in {x:entity & {_: pin x & {y:entity & {_: carrot y & when (fun t => aspT {x : entity & human x -> False} asp_pin (pull_out t (projT1 asp_pin) i ))
            (fun t => aspT {x : entity & human x -> False} asp_it ({x : entity & hole x && have t x (projT1 asp_it)}))}}}}.
    clear asp_pin asp_it.
    simple refine {x : entity &
       {s1 : pin x &
       {y : entity &
       {s2 : carrot y &
       {t1 : Q * Q &
       {t2 : Q * Q &
       {s3
       : aspT {x0 : entity & human x0 -> False} ?[asp1]
           (pull_out t1 (let (a, _) := ?asp1 in a) i) &
       {s4
       : aspT {x0 : entity & human x0 -> False} ?[asp2]
           {x0 : entity &
           {_ : hole x0 & have t2 x0 (let (a, _) := ?asp2 in a)}} &
       endtime t1 = endtime t2}}}}}}}}.
  tac1' 3%nat. (* a pin*)
  tac1' 4%nat.  (* a carrot *)
  Defined.

  Print ItHadAHole.

  Theorem inference2 : ItHadAHole -> {x : Q * Q &
       {x0 : entity &
       {_ : pin x0 &
       {x2 : entity & {_ : carrot x2 & stick_through x x0 x2 i}}}}}.
  Proof.
    clear asp_pin asp_it.
    tac3.
    specialize (axiom1 (q, q0) X1 (existT _ s (existT _ X3 X4))).
    destruct axiom1 as [t2 [y [H1 H2]]].
    exists t2.
    tac1.
  Defined.

  Theorem TimeOfPullOut : forall (a : ItHadAHole), time.
  Proof.
    intro.
    destruct a as [x1 [x2 [x3 [x4 [x5 H]]]]].
    exact x5.
  Defined.

  Theorem TimeOfHaveAHole : forall (a : ItHadAHole), time.
  Proof.
    intro.
    destruct a as [x1 [x2 [x3 [x4 [x5 [x6 H]]]]]].
    exact x6.
  Defined.

  Print TimeOfPullOut.

  Print TimeOfHaveAHole.
    
  Theorem inference2' : forall (a : ItHadAHole), {x : Q * Q &
       {x0 : entity &
         {_ : pin x0 &
           {x2 : entity & {_ : carrot x2 & {_ : stick_through x x0 x2 i & precede x (TimeOfHaveAHole a)}}}}}}.
  Proof.
    clear asp_pin asp_it.
    tac3.
    specialize (axiom1 (q, q0) X0 (existT _ s (existT _ X2 X3))).
    destruct axiom1 as [t2 [y [H1 [H2 H3]]]].
    exists t2.
    tac1.
  Defined.    


  Definition before (A B : time -> Type) : Type :=
    {t1 : time & {t2 : time & {s : A t1 & B t2 && (precede t1 t2)}}}.
  
  (* When I pulled the pin out, it (a carrot) had a hole.  => I stuck a pin through a carrot before a carrot had a hole.*)
  Theorem inference3 : ItHadAHole ->
                       before (fun t1 => a_acc pin (fun x z => a_acc carrot (stick_through t1 x) z) i)
                              (fun t2 => a_nom carrot (a_acc hole (have t2))).
  Proof.
    clear asp_pin asp_it.
    tac3.
    specialize (axiom1 (q, q0) X1 (existT _ s (existT _ X3 X4))).
    destruct axiom1 as [t2 [y [H0 [H1 H2]]]].
    exists t2.
    exists (q, q0).
    repeat try split; tac1.
  Defined.

  Theorem inference4 : forall (a : ItHadAHole), {x : Q * Q &
       {x0 : entity &
         {_ : pin x0 &
           {x2 : entity & {_ : carrot x2 & {_ : stick_through x x0 x2 i & precede x (TimeOfHaveAHole a)}}}}}}.
  Proof.
    clear asp_pin asp_it.
    tac3.
    specialize ( axiom1 (q, q0) X0 (existT _ s (existT _ X2 X3))).
    destruct axiom1 as [t2 [y [H1 [H2 H3]]]].
    exists t2.
    tac1.
  Defined.        

End When.


Section After.

  (* Joe paid a detective after he received a final report on the case. Cf. #213 of [1] *)

  Variable joe : entity.
  Variable detective man final_report_on_the_case : entity -> Type.
  Variable pay receive : time -> entity -> entity -> Type.
  Hypothesis JoeIsMan : man joe.
  Hypothesis ADetectiveIsAMan : forall x, detective x -> man x.

  Variable asp_he : {x : entity & man x}.
  
  Definition after (A B : time -> Type) : Type :=
    {t1 : time & {t2 : time & {s : A t1 & B t2 && (precede t2 t1)}}}.
  

  (* Joe paid a detective after he received a final report on the case. *)
  Theorem JoeReceive : Type.
  Proof.
    Eval cbv in after (fun t1 => a_acc detective (pay t1) joe)
                      (fun t2 => aspT {x : entity & man x} asp_he
                                      (a_acc final_report_on_the_case (receive t2) (projT1 asp_he))).
    clear asp_he.
    simple refine {t1 : Q * Q &
                  {t2 : Q * Q &
                  {s1 : {y : entity & {_ : detective y & pay t1 y joe}} &
                  {_
                  : aspT {x : entity & man x} ?[asp]
                  {y : entity & {_ : final_report_on_the_case y & receive t2 y (let (a, _) := ?asp in a)}} &
                      endtime t2 < (let (x, _) := t1 in x)}}}}.
    tac1' 3%nat.
  Defined.

  Print JoeReceive.

  Hypothesis PayDetective1 : forall t1 t2 : time, forall x y : entity,
      pay t1 y x -> detective y -> precede t2 t1 ->
      {z : entity & final_report_on_the_case z && receive t2 z y} -> False.
  
  (* he => detective *)
  Theorem DetectiveReceive : Type.
  Proof.
    Eval cbv in after (fun t1 => a_acc detective (pay t1) joe)
                      (fun t2 => aspT {x : entity & man x} asp_he
                                      (a_acc final_report_on_the_case (receive t2) (projT1 asp_he))).
    clear asp_he.
    simple refine {t1 : Q * Q &
                  {t2 : Q * Q &
                  {s1 : {y : entity & {_ : detective y & pay t1 y joe}} &
                  {_
                  : aspT {x : entity & man x} ?[asp]
                  {y : entity & {_ : final_report_on_the_case y & receive t2 y (let (a, _) := ?asp in a)}} &
                      endtime t2 < (let (x, _) := t1 in x)}}}}.
    tac1' 0%nat.
  Defined.

  Print DetectiveReceive.

  Theorem Contra2 : DetectiveReceive -> False.
  Proof.
    clear asp_he.
    tac5.
  Defined.

  Hypothesis axiom1 : forall (t1 : time) (x : entity),
      {y : entity & receive t1 y x} ->
        {t2 : time & {z : entity &
          {_ : pay t2 z x & precede t1 t2}}}.

  Hypothesis axiom2 : forall (t1 : time) (x : entity),
      {y : entity & {_ : final_report_on_the_case y & receive t1 y x}} ->
        {t2 : time & {z : entity & {_ : detective z &
          {_ : pay t2 z x & precede t1 t2}}}}.

  Theorem HeReceived : Type.
  Proof.
  Eval cbv in fun t => {joe:entity & {x:entity & {_: detective x &
    aspT{x:entity & man x} asp_he (a_acc final_report_on_the_case (receive t)(projT1 asp_he))}}}.
  simple refine { t : Q * Q &
       {s1 : entity &
       {x : entity &
       {s2 : detective x &
       aspT {x0 : entity & man x0} ?[asp]
         {y : entity &
         {s3 : final_report_on_the_case y & receive t y (let (a, _) := ?asp in a)}}}}}}.
  clear asp_he.
  exists joe.
  tac5. (* joe*)
  Defined.
  
  Theorem TimeOfHeReceived: HeReceived -> time.
  Proof.
    intro.
    destruct X as [x1 [x2 [x3 [x4 x5]]]].
    exact x1.
  Defined.
  
  (* He received the final report -> Joe paid the detective *)
  
  Compute fun t => a_acc detective (pay t) joe.
  
  Compute {x:Q * Q & {y : entity & {_ : detective y & pay x y joe}}}.
  
  Theorem inference6 : forall (a: HeReceived),
      {t : time & {y : entity & {_ : detective y & {_ : pay t y joe &  precede (TimeOfHeReceived a) t}}}}.
  Proof.
    clear asp_he.
    tac3.
  Defined.

  Print inference6.
  
End After.


Section Lawyer.
  
  Variables human lawyer man witness question: entity -> Type.
  Variable repeat answer: entity -> entity -> Type.
  Variables reluctant1 : entity -> Type.
  Definition reluctant2 : forall (n : entity -> Type)(x : entity), Type :=  fun n x => {_: n x & reluctant1 x}.

  Definition a_acc2 : forall (n : entity -> Type) (v: entity -> entity -> entity -> Type) (y x : entity), Type :=
  fun n v y x =>  {z : entity & {_ : n z & v x y z}}.

  Variable ask : entity -> entity -> entity -> Type.
  (*The lawyer asked the witness a question*)
  Compute (a_nom lawyer (a_acc question (a_acc2 witness ask))).
  (*he was reluctant to repeat it.*)
  Compute (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & man y}))).
  Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))(reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & man y})))).

  (* The lawyer asked the witness a question, but he was reluctant to answer it.
     Who was reluctant? => The witness  Cf. #10 of [1] *)
  
  Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))(reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & man y})))).

  Hypothesis AskAnswer :  forall x y z: entity, ask x y z-> answer y z .
  Hypothesis QuestionNotHuman : forall x:entity, question x -> (human x -> False).
  Hypothesis ManHuman : forall x:entity, man x -> human x.
  Hypothesis LawyerHuman : forall x:entity, lawyer x -> human x.
  Hypothesis WitnessHuman : forall x:entity, witness x -> human x.

  Theorem LawyerAsk: Type.
  Proof.
    Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))
          (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))).
   simple refine({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x3 & ask x x3 x1}}}}}} &
       (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & human y})))}).
    tac5.
    tac1.
  Defined.
  
  Print LawyerAsk.

  Theorem ex5: LawyerAsk -> a_nom witness reluctant1.
  Proof.
    tac1.
  Qed.

  (* The lawyer asked the witness a question, but he was reluctant to repeat it.
     Who was reluctant? => The lawyer  Cf. #9 of [1] *)
  
  Hypothesis RepeatReluctant :  forall x y: entity, repeat x y-> reluctant1 y .
  Theorem LawyerRepeat : Type.
  Proof.
    Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))
          (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))).
  simple refine ({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x & ask x x3 x1}}}}}} &
       (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))}).
    tac1.
    tac1.
  Defined.
  
  Theorem ex6: LawyerRepeat -> a_nom lawyer reluctant1.
  Proof.
    tac1.
  Qed.

  Theorem LawyerRepeat3 : Type.
  Proof.
    simple refine ({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x & ask x x3 x1}}}}}} &
           (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))}).
    assert Type.
    simple refine ({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x & ask x x3 x1}}}}}} &
           (reluctant2 (repeat (projT1 (?[asp3] : {x:entity & (human x -> False)})))(projT1 (?[asp4] : {y:entity &  human y})))}).
    - destruct s0 as [x [l [x1 [q [x3 [w a]]]]]].
      exists x1.
      apply QuestionNotHuman; assumption.
    - destruct s0 as [x [l [x1 [q [x3 [w a]]]]]].
      exact (existT _ x (LawyerHuman x l)).
    - tac1.
    - tac1.      
  Defined.

  Print LawyerRepeat3.

  Theorem LawyerRepeat4 : Type * Type.
  Proof.
    split.
    simple refine ({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x & ask x x3 x1}}}}}} &
           (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))}); tac1.
    simple refine ({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x & ask x x3 x1}}}}}} &
           (reluctant2 (repeat (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))}); tac1.
  Defined.

  Print LawyerRepeat4.

  Theorem LawyerAsk2: Type.
  Proof.
    Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))
          (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))).
    simple refine({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x3 & ask x x3 x1}}}}}} &
       (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & human y})))}).
    tac5.
    move_H' 5%nat.
    move_H; move_H; move_H.
    cbv in *; intros;
    try repeat (destruct_one_ex || destruct_one_pair || specialize_H || rewrite_H).
    eexists.
    apply_H.
  Defined.

  Theorem LawyerAsk' : Type * Type.
  Proof.
    Compute (prog_conj (a_nom lawyer (a_acc question (a_acc2 witness ask)))
          (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity &  human y})))).
    split.
    - simple refine({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x3 & ask x x3 x1}}}}}} &
       (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & human y})))}).
      tac5.
      tac1' 2%nat. (* he => the witness *)
    - simple refine({_
       : {x : entity &
         {_ : lawyer x &
         {x1 : entity &
         {_ : question x1 & {x3 : entity & {_ : witness x3 & ask x x3 x1}}}}}} &
       (reluctant2 (answer (projT1 (?[asp1] : {x:entity & (human x -> False)})))(projT1 (?[asp2] : {y:entity & human y})))}).
      tac5.
      tac1' 3%nat. (* he => the lawyer *)
  Defined.

  Print LawyerAsk'.

  Theorem Test0LawyerAsk' : fst LawyerAsk' * snd LawyerAsk' -> a_nom witness reluctant1.
  Proof.
    tac1.
  Defined.

  Theorem Test1LawyerAsk' : fst LawyerAsk' * snd LawyerAsk' -> a_nom lawyer reluctant1.
  Proof.
    tac1.
  Defined.

  Theorem Test2LawyerAsk' : fst LawyerAsk' -> a_nom witness reluctant1.
  Proof.
    tac1.
  Defined.

  Theorem Test3LawyerAsk' : fst LawyerAsk' -> a_nom lawyer reluctant1.
  Proof.
    tac1.
  Abort.

  Theorem Test4LawyerAsk' : snd LawyerAsk' -> a_nom lawyer reluctant1.
  Proof.
    tac1.
  Defined.

  Theorem Test5LawyerAsk' : snd LawyerAsk' -> a_nom witness reluctant1.
  Proof.
    tac1.
  Abort.
  
End Lawyer.
