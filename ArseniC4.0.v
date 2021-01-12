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
 | null : CExp
 | cuvant : ErrorString -> CExp.


Coercion cuvant : ErrorString >-> CExp.
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
 | fct_declare : string -> Stmt -> Stmt -> Stmt
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

Notation " 'switch' A 'inceput' 'case' a1 'sf' s1 'sfarsit' 'case' a2 'sf' s2 'sfarsit' 'default' s3 'sfarsit' " := (switch A a1 s1 a2 s2 s3) (at level 97).

Notation " 'declare' X S1 'begin' { S2 } 'endf' " := (fct_declare X S1 S2)(at level 78).
Notation " 'call' X 'endcall'" := (fct_call X)(at level 68).

Check (unsigned "a").
Check ("a" :n= 3).

Check (bool "a").
Check ("a" :b= bfalse).

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

Check ( switch "x" +' "y" inceput
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
declare "fun" unsigned "a" 
  begin
    {
      unsigned "b" ;;
      "b" :n= ("a" *' 10)
}endf
).

Check (call "fnct" endcall ).

Inductive Tipuri :=
 | error_undecl : Tipuri (* Sa nu folosesc variabile nedeclarate *)
 | error_assign : Tipuri (* Sa nu atribui valori de alt tip decat tipul variabilei *)
 | default : Tipuri (* O valoare default care se pune in variabile la declarere *)
 | tip_nat : ErrorNat -> Tipuri
 | tip_bul : ErrorBool -> Tipuri
 | tip_string : ErrorString -> Tipuri
 | code : Stmt -> Tipuri.


Check tip_nat.
Check tip_string.
Check tip_bul.
Check Tipuri.

Coercion tip_nat : ErrorNat >-> Tipuri.
Coercion tip_bul : ErrorBool >-> Tipuri.
Coercion tip_string : ErrorString >-> Tipuri.

Definition Egalitate_tipuri (t1 : Tipuri)(t2 : Tipuri) : bool :=
 match t1 with
 | error_assign => match t2 with  
                   | error_assign => true
                   | _ => false
                   end
 | error_undecl => match t2 with  
                   | error_undecl => true
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




































