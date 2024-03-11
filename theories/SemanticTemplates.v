Parameter entity : Type.

Definition a_nom : forall n v : entity -> Type, Type :=
  fun n v => {x : entity & {_ : n x & v x}}.

Definition a_acc : forall (n : entity -> Type) (v: entity -> entity -> Type) (x : entity), Type :=
  fun n v x =>  {y: entity & {_ : n y &  v y x}}.

Definition some_nom : forall n v : entity -> Type, Type :=
  fun n v => {x : entity & {_ : n x & v x}}.

Definition every_nom : forall n v : entity -> Type, Type :=
  fun n v => forall u : {x : entity & n x}, v (projT1 u).

Definition every_subj : (entity -> Type) -> (entity -> Type) -> Type :=
  fun (n : entity -> Type) (v : entity -> Type) => forall u : {x : entity & n x}, v (projT1 u). 

Definition every_obj : (entity -> Type) -> (entity -> entity -> Type) -> entity -> Type :=
  fun (n : entity -> Type) (p : entity -> entity -> Type) (x : entity) => forall u : {x : entity & n x}, p x (projT1 u). 

Definition no_nom : forall n v : entity -> Type, Type :=
    fun n v => {x : entity & {_ : n x & v x}} -> False.

Definition any_nom : forall n v : entity -> Type, Type :=
    fun n v => {x : entity & {_ : n x & v x}}.

Definition all_nom : forall n v : entity -> Type, Type :=
    fun n v => forall u : {x : entity & n x}, v (projT1 u).

Definition just_one_nom : forall n v : entity -> Type, Type :=
    fun n v => ({x : entity & {_ :  n x & v x}} * (forall y z : entity, {_ : {_ : {_: n y & v y} & n z} & v z} -> y = z))%type.

Definition who : forall (n v : entity -> Type) (x : entity), Type :=
    fun n v x => {_ : n x & v x}.

Definition if1 : Type -> Type -> Type :=
    fun p q => p -> q.

Definition prog_conj (A B : Type) : Type.
Proof.
  exact {_ : A & B}.
Defined.


(* 帰納的型として underspecified types (aspT) を定義する
   ただしこの型の要素は，自然数型や二分木(binary trees)型とは異なり，帰納的に定義されてはいない
   この意味では，単なるデータ型として aspT を定義していると言った方が正確

   型 aspT A a B で照応表現を含む文（例えば "He whistled."）を表すことを意図している
   Aにはholeの型が入り（例えば {x : entity & male x}），aにはholeが入る（例えば ?[asp1]）
   そしてBで照応表現を含む文を表す
  （例えばBを whistle (projT1 ?asp1) とおく
   ここで?[asp1]から [] を外したのは，こうしないとCoqがまた新しいholeが来たと勘違いするから）

   aspTの要素を構成するコンストラクタ resolve は，その名前の通り，
   照応を解決するようなオブジェクトを引数としてとる *)
  
Inductive aspT (A : Type) (a : A) (B : Type) : Type :=
    resolve : B -> aspT A a B.


(* 照応解析と，解析結果を用いた推論を同時に行うための型
   使用例は Anaphora.v を参照 *)

Definition resolution_record : Type := {A : Type & A}.  
