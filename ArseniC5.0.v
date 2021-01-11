(* Librariile necesare pt a lucra cu stringuri*)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope. 
Scheme Equality for string.

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
Check ("a" +' "b").
Check ("a" -' "b").
Check ("a" +' 3).
Check ("a" /' 0).
Check (7 %' 2).

(* Acum pentru expresii booleene *)
Inductive BExp :=
 | berror : ErrorBool -> BExp
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
Check (!' "a").
Check ("a" <' "b").
Check ("a" <=' "b").
Check ("a" >' "b").
Check ("a" >=' "b").
Check ("a" ||' "b").

(* Pentru expresii cu siruri de caractere *)

Inductive CExp :=
 | cstring : ErrorString -> CExp
 | cvar : string -> CExp.


Coercion cvar : string >-> CExp.
Scheme Equality for CExp.

(* Functii stringuri *) 

Definition append_s (c1 c2 : ErrorString) : ErrorString :=
  match c1, c2 with
    | error_string, _ => error_string
    | _, error_string => error_string
    | char c1, "" => error_string
    | "", char c2 => error_string
    | char c1, char c2 => char (append c1 c2)
  end.


Compute append "asd" "asd".
Compute append_s "asd" "asd".
Compute eqb "asd" "asd".

Definition equal_s (c1 c2 : ErrorString) : ErrorBool :=
  match c1, c2 with
    | error_string, _ => error_bool
    | _, error_string => error_bool
    | char c1, char c2 => bul (eqb c1 c2)
  end.

Compute length "asd".

Definition strlen_s (c1 : ErrorString) : ErrorNat :=
  match c1 with
    | error_string => error_nat
    | char c1 => num (length c1)
  end.

Compute strlen_s "asd".

Notation " A =s= B " := (equal_s A B) (at level 30).
Notation " 'strlen' ( A ) " := (strlen_s A) (at level 31).
Notation " A +s+ B " := (append_s A B) (at level 32).

Check strlen ( "abc" ).
Compute strlen ( "abc" ).
Compute "abc" =s= "abc".
Compute "abc" =s= "abcd".
Compute "te" +s+ " pup".

(* Functii castare *)

Definition b_to_str (b : bool) : ErrorString :=
  match b with
  | true => "true"
  | false => "false"
  end.

Notation "'(b_char)' { A }" := (b_to_str A)( at level 35).

Compute ((b_char) { true }).
Compute ((b_char) { false }).

Definition n_to_str (n : nat) : ErrorString :=
  match n with
  | 0 => "zero"
  | 1 => "unu"
  | 2 => "doi"
  | 3 => "trei"
  | 4 => "patru"
  | 5 => "cinci"
  | 6 => "sase"
  | 7 => "sapte"
  | 8 => "opt"
  | 9 => "noua"
  | _ => "numar din doua cifre"
  end.

Notation "'(n_char)' { A }" := (n_to_str A)( at level 35).

Compute ((n_char) { 5 }).
Compute ((n_char) { 11 }).


(* Definirea tipului pentru vectori cu ajutorul listelor*)

Inductive Vector :=
 | Error_vector : Vector
 | Nat_vector : nat -> list ErrorNat -> Vector
 | Bool_vector : nat -> list ErrorBool -> Vector
 | String_vector : nat -> list ErrorString -> Vector.

Check Nat_vector.

(* Statementuri *)

Inductive Stmt :=
 | nada : Stmt
 | nat_decl : string -> Stmt
 | nat_assign : string -> AExp -> Stmt
 | bool_decl : string -> Stmt
 | bool_assign : string -> BExp -> Stmt
 | string_decl : string -> Stmt
 | string_assign : string -> CExp -> Stmt
 | sequence : Stmt -> Stmt -> Stmt
 | nat_decl_vector : string -> Vector -> Stmt
 | nat_assign_vector : string -> Vector -> Stmt
 | bool_decl_vector : string -> Vector -> Stmt
 | bool_assign_vector : string -> Vector -> Stmt
 | string_decl_vector : string -> Vector -> Stmt
 | string_assign_vector : string -> Vector -> Stmt
 | while : BExp -> Stmt -> Stmt
 | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
 | ifthen : BExp -> Stmt -> Stmt
 | break : Stmt
 | continue : Stmt
 | fct_declare : string -> Stmt -> Stmt 
 | fct_call : string -> Stmt
 | switch : AExp -> AExp -> Stmt -> AExp -> Stmt -> Stmt -> Stmt.

Notation "'unsigned' X" := (nat_decl X)(at level 80).
Notation "'bool' X" := (bool_decl X)(at level 80).
Notation "'char' X" := (string_decl X)(at level 80).

Notation "V [ N ]n" := ( nat_decl_vector V num N)(at level 40).
Notation "V [ N ]b" := ( bool_decl_vector V num N)(at level 40).
Notation "V [ N ]s" := ( string_decl_vector V num N)(at level 40).

Notation "V [ N ]n={ E1 ; E2 ; .. ; En }" := ( nat_assign_vector V ( Nat_vector N (cons num(E1) (cons num(E2) .. (cons num(En) nil) ..) ) ) )(at level 40).
Notation "V [ N ]b={ E1 ; E2 ; .. ; En }" := ( bool_assign_vector V ( Bool_vector N (cons bul(E1) (cons bul(E2) .. (cons bul(En) nil) ..) ) ) )(at level 40).
Notation "V [ N ]s={ E1 ; E2 ; .. ; En }" := ( string_assign_vector V ( String_vector N (cons string(E1) (cons string(E2) .. (cons string(En) nil) ..) ) ) )(at level 40).

Notation "X :n= A" := (nat_assign X A)(at level 80).
Notation "X :b= A" := (bool_assign X A)(at level 80).
Notation "X :s= A" := (string_assign X A)(at level 80).

Notation "S1 ;; S2" := (sequence S1 S2)(at level 93).

Notation "'if'' B 'then'' S1 'end''" := (ifthen B S1)(at level 83).
Notation "'if'' B 'then'' S1 'else'' S2 'end''" := (ifthenelse B S1 S2)(at level 83).
Notation "'for' ( A ~ B ~ C ) { S }" := (A ;; while B  (S ;; C )) (at level 97).
Notation "'while'' ( B ) { S }" := (while B S) (at level 83).

Notation " 'switch'' A 'inceput' 'case' a1 'sf' s1 'sfarsit' 'case' a2 'sf' s2 'sfarsit' 'default' s3 'sfarsit' " := (switch A a1 s1 a2 s2 s3) (at level 97).

Notation " 'declare' X 'begin' { S1 } 'endf' " := (fct_declare X S1 )(at level 78).
Notation " 'call' X 'endcall'" := (fct_call X)(at level 68).

Check (unsigned "a").
Check ("a" :n= 3).

Check (bool "a").


Check (char "c").
Check ("c" :s= "abc").

Check (

unsigned "a";;
unsigned "b";;
unsigned "sum";;
"sum" :n= 0;;
"a" :n= 1;;
"b" :n= 5;;
char "rasp";;

if' ("a" <=' "b") then'
  "rasp" :s= "a este mai mic sau egal cu b"
else'
  "rasp" :s= "a este mai mare decat b"
end'
).

Check ( switch' "x" +' "y" inceput
          case 7 sf "z" :n= 7 sfarsit
          case 10 sf "z" :n= 10 sfarsit
          default "z" :n= 0 sfarsit  ).


Check (

unsigned "x";;
unsigned "y";;
"x" :n= 1;;
"y" :n= 4;;
while' ( "x" <' "y" ) {
  "x" :n= "x" +' 1;;
  if' ("x" ==' 2 ) then'
      break 
  end'
}
).

Check (
declare "fun"
  begin
    {
      unsigned "b" ;;
      "b" :n= ("a" *' 10)
}endf
).

Check (call "fnct" endcall ).

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
Compute eqb "asd" "asd".
Compute length "asd".

Definition equal_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => bul (Nat.eqb v1 v2)
  end.

(* Functia de castare *)

Definition nat_to_bool (n : nat) : ErrorBool :=
  match n with
  | 0 => false
  | _ => true
  end.

Notation "'(n_bool)' { A }" := (nat_to_bool A)( at level 35).

Compute nat_to_bool 12.
Compute nat_to_bool 0.
Compute ((n_bool) { 123 }).

Inductive Tipuri :=
 | error_undecl : Tipuri (* Sa nu folosesc variabile nedeclarate *)
 | error_assign : Tipuri (* Sa nu atribui valori de alt tip decat tipul variabilei *)
 | default : Tipuri (* O valoare default care se pune in variabile la declarere *)
 | tip_nat : ErrorNat -> Tipuri
 | tip_string : ErrorString -> Tipuri
 | tip_bul : ErrorBool -> Tipuri
 | code : Stmt -> Tipuri.


Check tip_nat.
Check tip_string.
Check tip_bul.
Check Tipuri.

Coercion tip_nat : ErrorNat >-> Tipuri.


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
 | tip_nat x => match t2 with  
                   | tip_nat x => true
                   | _ => false
                   end
 | tip_bul x => match t2 with  
                   | tip_bul x => true
                   | _ => false
                   end
 | tip_string x => match t2 with
                   | tip_string x => true
                   | _ => false
                  end
 | code x => match t2 with
                   | code x => true
                   | _ => false
                  end
end.

Check Egalitate_tipuri.
Check tip_nat.

Definition Env := string -> Tipuri.

(* Acum fac functia de atribuire a unei valori unei variabile*)

Definition update (env : Env) (x : string) (v : Tipuri ) : Env :=
  fun y =>
    if (eqb y x)
    then
      if(and_ErrorBool ( Egalitate_tipuri (error_undecl) (env y)) (not_ErrorBool (Egalitate_tipuri (default) (v))))
      then error_undecl
      else
        if(and_ErrorBool (Egalitate_tipuri (error_undecl) (env y))(Egalitate_tipuri (default) (v)))
        then default
        else
          if(or_ErrorBool (Egalitate_tipuri (default) (env y))(Egalitate_tipuri (v) (env y)))
          then v
          else error_assign
    else (env y).


Definition env0 : Env := fun n => error_undecl.
Definition env1 : Env := fun x => 5.

(* Semnatica expresii aritmetice *)

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

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, 0 => error_nat
    | num v1, num v2 => (Nat.div v1 v2) 
  end.
Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, 0 => error_nat
    | num v1, num v2 => (Nat.modulo v1 v2) 
  end.

Check mod_ErrorNat.

(* Functiile pentru castare *)

Definition bool_to_nat (b : ErrorBool) : ErrorNat :=
  match b with 
  | error_bool => error_nat 
  | bul a => match a with 
          | true => 1
          | false => 0
          end
  end.

Notation "'(b_nat)' { A }" := (bool_to_nat A)( at level 35).

Compute bool_to_nat true.
Compute bool_to_nat false.
Compute ((b_nat) { false }).

Definition str_to_nat (s : string) : ErrorNat :=
  match s with 
  | unu => 1
  end.

Notation "'(s_nat)' { A }" := (str_to_nat A)( at level 35).

Compute str_to_nat "unu".
Compute ((s_nat) { "unu" }).
(* Aici am dat peste o problema de redundanta *)

Fixpoint aeval_fun (a : AExp) (sigma : Env) : ErrorNat :=
  match a with
  | anum n => match n with
              | error_nat => error_nat
              | num n' => n'
              end
  | avar v => match (sigma v) with
              | tip_nat y => match y with
                                  | error_nat => error_nat
                                  | num y' => y'
                                  end
              | _ => error_nat
              end
  | aplus a1 a2 => plus_ErrorNat (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | aminus a1 a2 => minus_ErrorNat (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | amul a1 a2 => mul_ErrorNat (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | adiv a1 a2 => div_ErrorNat (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | amod a1 a2 => mod_ErrorNat (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  end.

Compute aeval_fun (3 +' 3 *' 3) env0.

(* Am pus si semantica Big Step pentru expresii aritmetice*)
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

Example eroare_la_dif : 2 -' 3 =[ env0 ]=> error_nat.
Proof.
  eapply dif.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed.
Example eroare_la_div : 9 /' 0 =[ env0 ]=> error_nat.
Proof.
  eapply div.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed.
Example eroare_la_mod : 5 %' 0 =[ env0 ]=> error_nat.
Proof.
  eapply modd.
    - apply const.
    - apply const.
    - simpl. reflexivity.
Qed.
Example plus_bun : 5 +' "x" =[ env1 ]=> 10.
Proof.
  eapply add.
    - apply const.
    - apply var.
    - simpl. reflexivity.
Qed. 

(* Semnatica pt expresii booleene *)

Fixpoint beval_fun (b : BExp) (sigma : Env) : ErrorBool :=
  match b with
  | berror x => match x with
                | error_bool => error_bool
                | bul x' => x'
                end
  | bvar v => match (sigma v) with
              | tip_bul y => match y with
                                  | error_bool => error_bool
                                  | bul y' => y'
                                  end
              | _ => error_bool
              end
  | blessthan a1 a2 => (lessthan_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | beqlessthan a1 a2 => (lessthan_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bgreaterthan a1 a2 => (greaterthan_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | beqgreaterthan a1 a2 => (greaterthan_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bnot a1 => (not_ErrorBool (beval_fun a1 sigma))
  | band a1 a2 => (and_ErrorBool (beval_fun a1 sigma) (beval_fun a2 sigma))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 sigma) (beval_fun b2 sigma))
  | bequal b1 b2 => (equal_ErrorBool (aeval_fun b1 sigma) (aeval_fun b2 sigma))
  end.

(* Am pus si semantica Big Step pentru expresii booleene*)

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
 | e_error : forall sigma x,
   berror x ={ sigma }=> match x with
                           | error_bool => error_bool
                           | bul x' => x' 
                         end
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

Example eroare_bool : band (10 <=' 5) (100 >=' "n") ={ env0 }=> error_bool.
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

(* Am pus si semantica Big Step pentru operatii pe stringuri*)

Reserved Notation "C -[ S ]-> C'" (at level 70).
Inductive ceval : CExp -> Env -> ErrorString -> Prop :=
 | c_const : forall sigma s, cstring s -[ sigma ]-> s
 | c_var : forall c sigma, cvar c -[ sigma ]-> match (sigma c) with
                                               | tip_string x => x
                                               | _ => error_string
                                             end 
where "c -[ sigma ]-> c'" := ( ceval c sigma c').

(* Semantica pentru statementuri *)

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl : forall x sigma sigma',
  sigma' = (update sigma x (default)) -> (unsigned x) -{ sigma }-> sigma'
| e_nat_assign : forall a i x sigma sigma',
  a =[ sigma ]=> i ->
  sigma' = (update sigma x (tip_nat i)) -> (x :n= a) -{ sigma }-> sigma'
| e_bool_decl : forall x sigma sigma',
  sigma' = (update sigma x (default)) -> (bool x) -{ sigma }-> sigma'
| e_bool_assign : forall a i x sigma sigma',
  a ={ sigma }=> i ->
  sigma' = (update sigma x (tip_bul i)) -> (x :b= a) -{ sigma }-> sigma'
| e_string_decl : forall x sigma sigma',
  sigma' = (update sigma x (default)) -> (char x) -{ sigma }-> sigma'
| e_string_assign : forall a i x sigma sigma',
  a -[ sigma ]-> i ->
  sigma' = (update sigma x (tip_string i)) -> (x :s= a) -{ sigma }-> sigma'
| e_sequence: forall s1 s2 sigma sigma1 sigma2,
  s1 -{ sigma }-> sigma1 ->
  s2 -{ sigma }-> sigma2 -> (s1 ;; s2) -{ sigma }-> sigma2
| e_ifThen : forall s b sigma sigma',
  b ={ sigma }=> true ->
  s -{ sigma }-> sigma' -> (if' b then' s end') -{ sigma }-> sigma'
| e_iftrue : forall sigma sigma' b s1 s2,
  b ={ sigma }=> true ->
  s1 -{ sigma }-> sigma' -> (if' b then' s1 else' s2 end')  -{ sigma }-> sigma'
| e_iffalse : forall sigma sigma' b s1 s2,
  b ={ sigma }=> false ->
  s2 -{ sigma }-> sigma' -> (if' b then' s1 else' s2 end') -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
  b ={ sigma }=> false -> while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
  b ={ sigma }=> true ->
  (s ;; while b s) -{ sigma }-> sigma' -> while b s -{ sigma }-> sigma'
| e_fct_declare : forall sigma sigma' nume s,
    sigma' = update sigma nume (code s) ->
    (fct_declare nume s) -{ sigma }-> sigma'
| e_fct_call : forall s X sigma sigma',
    s = match (sigma X) with
        | code y => y
        | _ => nada
        end ->
    s -{ sigma }-> sigma' ->
    (fct_call X) -{ sigma }-> sigma'
| e_switch_case1 : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a1) ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    (switch A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
| e_switch_case2 : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a2) ={ sigma }=> true ->
    s2 -{ sigma }-> sigma' ->
    (switch A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
| e_switch_default : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a1) ={ sigma }=> false ->
    (a ==' a2) ={ sigma }=> false ->
    s3 -{ sigma }-> sigma' ->
    (switch A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


Example decl_assign_nat : exists sigma1, (unsigned "a" ;; "a" :n= 10) -{ env0 }-> sigma1.
Proof.
  eexists.
  eapply e_sequence.
  - eapply e_nat_decl. reflexivity.
  - eapply e_nat_assign.
    + eapply const.
    + reflexivity.
Qed.

























