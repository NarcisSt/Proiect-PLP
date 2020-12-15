(* Librariile necesare pt a lucra cu stringuri*)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope. 
Scheme Equality for string.

(* Librariile necesare pt a lucra cu int *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Librariile necesare pentru a lucra cu liste *)
Require Import Coq.Lists.List.
Import ListNotations.
Scheme Equality for list.

(* Acum voi inlocui tipul nat pe care l am mai folosit cu un nou tip: ErrorNar, care trateaza si cazurile mai speciale *)
Inductive ErrorNat :=
 | error_nat: ErrorNat
 | num : nat -> ErrorNat.
Check ErrorNat.
Check error_nat.
Check num.
Coercion num : nat >-> ErrorNat.

(* La fel pentru int *)

Inductive ErrorInt :=
 | error_int : ErrorInt
 | int : Z -> ErrorInt.
Check ErrorInt.
Check error_int.
Check int.
Coercion int : Z >-> ErrorInt.
 
(* Same pentru bool *)

Inductive ErrorBool :=
 | error_bool : ErrorBool
 | bul : bool -> ErrorBool.
Check ErrorBool.
Check error_bool.
Check bul.
Coercion bul : bool >-> ErrorBool.

(* Fac un tip cu erori si pentru string, pentru moment*)

Inductive ErrorString :=
 | error_string : ErrorString
 | char : string -> ErrorString.
Check ErrorString.
Check error_string.
Check char.
Coercion char : string >-> ErrorString.

(* Pentru expr aritmetice *)
Inductive AExp := 
 | anum : ErrorNat -> AExp
 | avar : string -> AExp
 | aint : ErrorInt -> AExp
 | aplus : AExp -> AExp -> AExp
 | aminus : AExp -> AExp -> AExp
 | amul : AExp -> AExp -> AExp
 | adiv : AExp -> AExp -> AExp
 | amod : AExp -> AExp -> AExp.

Coercion avar : string >-> AExp.
Coercion anum : ErrorNat >-> AExp.
Coercion aint : ErrorInt >-> AExp.

Notation "A +' B" := (aplus A B)(at level 60, right associativity).
Notation "A -' B" := (aminus A B)(at level 60, right associativity).
Notation "A *' B" := (amul A B)(at level 59, right associativity).
Notation "A /' B" := (adiv A B)(at level 59, right associativity).
Notation "A %' B" := (amod A B)(at level 58, right associativity).
Check ("a" +' "b").
Check ("a" -' "b").
Check ("a" +' 3).
Check ("a" -' (-5)).
Check ("a" /' 0).
Check (7 %' 2).

(* Acum pentru expresii booleene *)
Inductive BExp :=
 | berror 
 | btrue
 | bfalse
 | bvar : string -> BExp
 | blessthan : AExp -> AExp -> BExp
 | beqlessthan : AExp -> AExp -> BExp
 | bgreaterthan : AExp -> AExp -> BExp
 | beqgreaterthan : AExp -> AExp -> BExp
 | bnot : BExp -> BExp
 | band : BExp -> BExp -> BExp
 | bor : BExp -> BExp -> BExp
 | bequal : AExp -> AExp -> BExp.

Coercion bvar : string >-> BExp.

Notation "A <' B" := (blessthan A B) (at level 53).
Notation "A <=' B" := (beqlessthan A B) (at level 53).
Notation "A >' B" := (bgreaterthan A B) (at level 53).
Notation "A >=' B" := (beqgreaterthan A B) (at level 53).
Notation "!' A" := (bnot A) (at level 50, left associativity).
Notation "A &&' B" := (band A B) (at level 51, left associativity).
Notation "A ||' B" := (bor A B) (at level 52, left associativity). 
Notation "A ==' B" := (bequal A B) (at level 54, left associativity).
Check berror.
Check btrue.
Check bfalse.
Check (!' "a").
Check (!' btrue).
Check ("a" <' "b").
Check ("a" <=' "b").
Check ("a" >' "b").
Check ("a" >=' "b").
Check ("a" &&' bfalse).
Check ("a" ||' "b").


(* Pentru expresii cu siruri de caractere *)

Inductive CExp :=
 | cconst : ErrorString -> CExp
 | cvar : string -> CExp
 | cequal : ErrorString -> ErrorString -> CExp
 | clength : ErrorString -> CExp
 | cappend : ErrorString -> ErrorString -> CExp.

Coercion cvar : string >-> CExp.

Notation " A =s= B " := (cequal A B) (at level 30).
Notation " 'length' ( A ) " := (clength A) (at level 31).
Notation " A +s+ B " := (cappend A B) (at level 32).

Check ("asd" =s= "asd").
Check (length ( "asd" )).
Check ("asd" +s+ "fgh").

(* Statementuri *)
Print Coq.Lists.List.

Inductive Stmt :=
 | nat_decl : string -> Stmt
 | nat_assign : string -> AExp -> Stmt
 | int_decl : string -> Stmt
 | int_assign : string -> AExp -> Stmt
 | bool_decl : string -> Stmt
 | bool_assign : string -> BExp -> Stmt
 | string_decl : string -> Stmt
 | string_assign : string -> CExp -> Stmt
 | sequence : Stmt -> Stmt -> Stmt
 | while : BExp -> Stmt -> Stmt
 | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
 | ifthen : BExp -> Stmt -> Stmt
 | fct_declare : string -> Stmt -> Stmt -> Stmt
 | fct_call : string -> list Z -> Stmt
 | switch : AExp -> list Case -> Stmt
 with Case :=
 | case : AExp -> Stmt -> Case
 | default' : Stmt -> Case.

Notation "'unsigned' X" := (nat_decl X)(at level 80).
Notation "'int' X" := (int_decl X)(at level 80).
Notation "'bool' X" := (bool_decl X)(at level 80).
Notation "'char' X" := (string_decl X)(at level 80).

Notation "X :n= A" := (nat_assign X A)(at level 80).
Notation "X :i= A" := (int_assign X A)(at level 80).
Notation "X :b= A" := (bool_assign X A)(at level 80).
Notation "X :s= A" := (string_assign X A)(at level 80).

Notation "S1 ;; S2" := (sequence S1 S2)(at level 93).

Notation "'if'' B 'then'' S1 'end''" := (ifthen B S1)(at level 83).
Notation "'if'' B 'then'' S1 'else'' S2 'end''" := (ifthenelse B S1 S2)(at level 83).
Notation "'for' ( A ~ B ~ C ) { S }" := (A ;; while B  (S ;; C )) (at level 97).
Notation "'while'' ( B ) { S }" := (while B S) (at level 83).

Notation " 'switch' A 'en' L 'ends' " := (switch A L)(at level 83).
Notation " 'case' A 'en' S 'en' " := (case A S)(at level 84).
Notation " 'default'' S 'en'" := (default' S)(at level 84).

Notation " 'declare' X S1 'begin' { S2 } 'endf' " := (fct_declare X S1 S2)(at level 78).
Notation " 'call' X 'begin' L 'endf'" := (fct_call X L)(at level 68).

Check (unsigned "a").
Check ("a" :n= 3).

Check (bool "a").
Check ("a" :b= bfalse).

Check (char "c").
Check ("c" :s= "abc").

Check (

int "a";;
int "b";;
int "sum";;
"sum" :n= 0;;
"a" :i= 1;;
"b" :i= 5;;
char "rasp";;

if' ("a" <=' "b") then'
  "rasp" :s= "a este mai mic sau egal cu b"
else'
  "rasp" :s= "a este mai mare decat b"
end'
).

Check (

switch 6 en [
  case 6 en "c" :i= 6 en ;
  case 9 en "c" :i= 9 en ;
  default' "c" :i= -1 en
]
ends
).

Check (
declare "fun" int "a" 
  begin
    {
      int "b" ;;
      "b" :i= ("a" *' 10)
}endf
).

Check (call "fun" begin [10;20] endf).




(* Creez un tip in care adun toate celelalte tipuri *)

Inductive Tipuri :=
 | error_undecl : Tipuri (* Sa nu folosesc variabile nedeclarate *)
 | error_assign : Tipuri (* Sa nu atribui valori de alt tip decat tipul variabilei *)
 | default : Tipuri (* O valoare default care se pune in variabile la declarere *)
 | tip_nat : ErrorNat -> Tipuri
 | tip_bul : ErrorBool -> Tipuri
 | tip_int : ErrorInt -> Tipuri
 | tip_string : ErrorString -> Tipuri
 | code : Stmt -> Tipuri.

Check tip_nat.
Check tip_string.
Check tip_int.
Check tip_bul.
Check Tipuri.

(* Scheme Equality for Tipuri. *)

(* Deoarece am construit tipul "Tipuri", nu mai trebuie sa fac cate un enviroment pentru toate tipurile, ci doar pentru el*)
Definition Env := string -> Tipuri.

(* Functie pentru egalitatea pe tipuri *)

Definition Egalitate_tipuri (t1 : Tipuri)(t2 : Tipuri) : ErrorBool :=
 match t1 with
 | error_undecl => match t2 with  
                   | error_undecl => true
                   | _ => false
                   end
 | error_assign => match t2 with  
                   | error_assign => true
                   | _ => false
                   end
 | default => match t2 with  
                   | default => true
                   | _ => false
                   end
 | tip_nat _x => match t2 with  
                   | tip_nat _y => true
                   | _ => false
                   end
 | tip_bul _x => match t2 with  
                   | tip_bul _y => true
                   | _ => false
                   end
 | tip_string _x => match t2 with
                   | tip_string _y => true
                   | _ => false
                  end
 | tip_int _x => match t2 with  
                   | tip_int _y => true
                   | _ => false
                   end
 | code _x => match t2 with  
                   | code _y => true
                   | _ => false
                   end
 end.
Check Egalitate_tipuri.
Check tip_nat.
(* Definesc un environment in care practic spun ca initial nici o variabila nu este declarata*)
Definition env : Env := fun x => error_undecl. 
 Check (env "x").
Compute (env "x"). 

(* Acum fac functia de atribuire a unei valori unei variabile*)

(* Definition update (env : Env) (x : string) (v : Tipuri ) : Env :=
  fun y =>
    if (eqb y x)
    then
      if(andb (Egalitate_tipuri error_undecl (env y)) (negb (Egalitate_tipuri default v)))
      then error_undecl
      else
        if(andb (Egalitate_tipuri error_undecl (env y))(Egalitate_tipuri default v))
        then default
        else
          if(orb (Egalitate_tipuri default (env y))(Egalitate_tipuri v (env y)))
          then v
          else error_assign
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 1).

Check (update env "y" default).
Compute (update (update env "y" (default)) "y" (tip_bul true) "y").
 *)
(* Este nevoie de anumite functii pentru a trata si cazurile cu erori, cate o functie pentru fiecare operatie*)

(* Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
  end. 

Compute plus_ErrorNat 1 2.

Definition minus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => if (Nat.leb v1 v2)
                        then error_nat
                        else num (v1 - v2)
  end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
  end.
Import Nat.
Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, 0 => error_nat
    | num v1, num v2 => (div v1 v2) 
  end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, 0 => error_nat
    | num v1, num v2 => (modulo v1 v2) 
  end.

Check mod_ErrorNat.
(* Am pus si semantica Big Step pentru a face exemplele*)

Reserved Notation "A =[ S ]=> N" (at level 70).
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
 | const : forall n sigma, anum n =[ sigma ]=> n
 | var : forall v sigma, avar v =[ sigma ]=> match (sigma v) with
                                               | tip_nat x => x
                                               | _ => error_nat
                                             end
 | add : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = (plus_ErrorNat i1 i2) -> (a1 +' a2) =[ sigma ]=> n
 | dif : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = (minus_ErrorNat i1 i2) -> a1 -' a2 =[ sigma ]=> n
 | times : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = (mul_ErrorNat i1 i2) -> a1 *' a2 =[ sigma ]=> n
 | div : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = (div_ErrorNat i1 i2) -> a1 /' a2 =[ sigma ]=> n
 | modd : forall a1 a2 i1 i2 sigma n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = mod_ErrorNat i1 i2 -> a1 %' a2 =[ sigma ]=> n
where "a =[ sigma ]=> n" := ( aeval a sigma n).

Example eroare_la_dif : 2 -' 3 =[ env ]=> error_nat.
Proof.
  eapply dif.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed.

Example eroare_la_div : 9 /' 0 =[ env ]=> error_nat.
Proof.
  eapply div.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed.

Example eroare_la_mod : 5 %' 0 =[ env ]=> error_nat.
Proof.
  eapply modd.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed. *)



(* Asemanator ca la numerele naturale, fac functii pentru fiecare operatie, deoarece au aparut cazurile in care pot avea erori*)

(* Definition lessthan_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => bul (Nat.ltb v1 v2)
  end.

Definition greaterthan_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => bul (negb (Nat.leb v1 v2))
  end.

Definition not_ErrorBool (n : ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | bul v => bul (negb v)
  end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | bul v1, bul v2 => bul (andb v1 v2)
  end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | bul v1, bul v2 => bul (orb v1 v2)
  end.

Definition equal_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => bul (eqb v1 v2)
  end.
Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
 | e_error : forall sigma,
  berror ={ sigma }=> error_bool
 | e_true : forall sigma,
  btrue ={ sigma }=> true
 | e_false : forall sigma,
  bfalse ={ sigma }=> false
 | e_var : forall v sigma,
  bvar v ={ sigma }=> match (sigma v) with
                        | tip_bul x => x
                        | _ => error_bool
                      end
 | e_lessthan : forall a1 a2 i1 i2 sigma b,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b = (lessthan_ErrorBool i1 i2) -> a1 <=' a2 ={ sigma }=> b
 | e_greaterthan : forall a1 a2 i1 i2 sigma b,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b = (greaterthan_ErrorBool i1 i2) -> a1 >=' a2 ={ sigma }=> b
 | e_not : forall a1 i1 sigma b,
  a1 ={ sigma }=> i1 ->
  b = (not_ErrorBool i1) -> !' a1 ={ sigma }=> b
 | e_and : forall a1 a2 i1 i2 sigma b,
  a1 ={ sigma }=> i1 ->
  a2 ={ sigma }=> i2 ->
  b = (and_ErrorBool i1 i2) -> (a1 &&' a2) ={ sigma }=> b
 | e_or : forall a1 a2 i1 i2 sigma b,
  a1 ={ sigma }=> i1 ->
  a2 ={ sigma }=> i2 ->
  b = (or_ErrorBool i1 i2) -> (a1 ||' a2) ={ sigma }=> b
 | e_equal : forall a1 a2 i1 i2 sigma b,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  b = (equal_ErrorBool i1 i2) -> a1 ==' a2 ={ sigma }=> b
where "B ={ S }=> B'" := ( beval B S B').

Example eroare_bool : band (10 <=' 5) (100 >=' "n") ={ env }=> error_bool.
Proof.
  eapply e_and.
    - eapply e_lessthan.
      + apply const.
      + apply const.
      + auto.
    - eapply e_greaterthan.
      + apply const.
      + apply var.
      + simpl. auto.
    - simpl. reflexivity.
Qed.
 *)


(* Functii stringuri *)

(* Definition equal_ErrorString (c1 c2 : ErrorString) : ErrorBool :=
  match c1, c2 with
    | error_string, _ => error_bool
    | _, error_string => error_bool
    | char c1, char c2 => bul (eqb c1 c2)
  end.

Definition append_ErrorString (c1 c2 : ErrorString) : ErrorString :=
  match c1, c2 with
    | error_string, _ => error_string
    | _, error_string => error_string
    | char c1, "" => error_string
    | "", char c2 => error_string
    | char c1, char c2 => char (append c1 c2)
  end.

(* Definition length_ErrorString (c1 : ErrorString) : ErrorNat :=
  match c1 with
    | error_string => error_nat
    | char c1 => num (length c1)
  end. Bug aici, sa revii!! *)

Reserved Notation "C -[ S ]-> C'" (at level 70).
Inductive ceval : CExp -> Env -> ErrorString -> Prop :=
 | const : forall c sigma, cconst c -[ sigma ]-> c
 | var : forall c sigma, cvar c -[ sigma ]-> match (sigma c) with
                                               | tip_string x => x
                                               | _ => error_string
                                             end
 | equal : forall c1 c2 i1 i2 sigma s,
  c1 -[ sigma ]-> i1 ->
  c2 -[ sigma ]-> i2 ->
  s = (equal_ErrorString i1 i2) -> (c1 =s= c2) -[ sigma ]-> s
 | append : forall c1 c2 i1 i2 sigma s,
  c1 -[ sigma ]-> i1 ->
  c2 -[ sigma ]-> i2 ->
  s = (append_ErrorString i1 i2) -> (c1 =s= c2) -[ sigma ]-> s
 | length : forall c1 i1 sigma s,
  c1 -[ sigma ]-> i1 -> s = (length_ErrorString i1) -> ( length ( c1 )) -[ sigma ]-> s
where "c -[ sigma ]-> c'" := ( ceval c sigma c'). *)



















































