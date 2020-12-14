Require Import Arith.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Ascii.
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope. 
Scheme Equality for string.

(* Librariile necesare pt a lucra cu stringuri*)

(* Acum voi inlocui tipul nat pe care l am mai folosit cu un nou tip: ErrorNar, care trateaza si cazurile mai speciale *)
Inductive ErrorNat :=
 | error_nat: ErrorNat
 | num : nat -> ErrorNat.
Check ErrorNat.
Check error_nat.
Check num.
Coercion num : nat >-> ErrorNat.

(* Same pentru bool *)

Inductive ErrorBool :=
 | error_bool : ErrorBool
 | bul : bool -> ErrorBool.
Check ErrorBool.
Check error_bool.
Check bul.
Coercion bul : bool >-> ErrorBool.

(* Creez tipul pentru stringuri ca siruri de caractere ascii *)


Inductive string : Type :=
  | EmptyString : string
  | String : ascii -> string -> string.


Delimit Scope string_scope with string.
Local Open Scope string_scope.


(* Creez un tip in care adun toate celelalte tipuri *)

Inductive Tipuri :=
 | error_undecl : Tipuri (* Sa nu folosesc variabile nedeclarate *)
 | error_assign : Tipuri (* Sa nu atribui valori de alt tip decat tipul variabilei *)
 | default : Tipuri (* O valoare default care se pune in variabile la declarere (0 pt num, false pt bul si " " pt char) *)
 | tip_nat : ErrorNat -> Tipuri
 | tip_bul : ErrorBool -> Tipuri
 | tip_char : string -> Tipuri.
Check tip_nat.
Check tip_char.

(* Scheme Equality for Tipuri. *)

(* Deoarece am construit tipul "Tipuri", nu mai trebuie sa fac cate un enviroment pentru toate tipurile, ci doar pentru el*)
Definition Env := string -> Tipuri.

(* Functie pentru egalitatea pe tipuri *)

Definition Egalitate_tipuri (t1 : Tipuri)(t2 : Tipuri) : bool :=
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
 | tip_char _x => match t2 with
                   | tip_char _y => true
                   | _ => false
                  end

 end.

Compute (Egalitate_tipuri (tip_nat 2)(tip_nat 123)).
Compute (Egalitate_tipuri (tip_nat 2)(tip_bul true)).

(* Definesc un environment in care practic spun ca initial nici o variabila nu este declarata*)
Definition env : Env := fun x => error_undecl. 
(* Check (env "x").
Compute (env "x"). *)

(* Acum fac functia de atribuire a unei valori unei variabile*)

Definition update (env : Env) (x : string) (v : Tipuri ) : Env :=
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

(* Pentru nr. naturale *)
Inductive AExp := 
 | anum : ErrorNat -> AExp
 | avar : string -> AExp
 | aplus : AExp -> AExp -> AExp
 | aminus : AExp -> AExp -> AExp
 | amul : AExp -> AExp -> AExp
 | adiv : AExp -> AExp -> AExp
 | amod : AExp -> AExp -> AExp.

Coercion avar : string >-> AExp.
Coercion anum : ErrorNat >-> AExp.

Notation "A +' B" := (aplus A B)(at level 60, right associativity).
Notation "A -' B" := (aminus A B)(at level 60, right associativity).
Notation "A *' B" := (amul A B)(at level 59, right associativity).
Notation "A /' B" := (adiv A B)(at level 59, right associativity).
Notation "A %' B" := (amod A B)(at level 58, right associativity).

(* Este nevoie de anumite functii pentru a trata si cazurile cu erori, cate o functie pentru fiecare operatie*)

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
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
Qed.


(* Acum pentru booleene *)
Inductive BExp :=
 | berror 
 | btrue
 | bfalse
 | bvar : string -> BExp
 | blessthan : AExp -> AExp -> BExp
 | bgreaterthan : AExp -> AExp -> BExp
 | bnot : BExp -> BExp
 | band : BExp -> BExp -> BExp
 | bor : BExp -> BExp -> BExp
 | bequal : AExp -> AExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A >=' B" := (bgreaterthan A B) (at level 53).
Notation "!' A" := (bnot A) (at level 50, left associativity).
Notation "A &&' B" := (band A B) (at level 51, left associativity).
Notation "A ||' B" := (bor A B) (at level 52, left associativity). 
Notation "A ==' B" := (bequal A B) (at level 54, left associativity).

(* Asemanator ca la numerele naturale, fac functii pentru fiecare operatie, deoarece au aparut cazurile in care pot avea erori*)

Definition lessthan_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
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

(* Pentru siruri de caractere *)

Inductive CExp :=
 | cchar : Char -> CExp
 | cvar : string -> CExp.

Coercion cchar : Char >-> CExp.
Coercion cvar : string >-> CExp.

(* Functii pentru char-uri *)

Local Open Scope lazy_bool_scope.
 
Fixpoint Equal_strings (s1 s2 : Char) : ErrorBool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ( Ascii.eqb c1 c2 &&& Equal_strings s1' s2')
 | _,_ => false
 end.

Check Equal_strings.
Compute  Equal_strings "asd" "asd".
  























