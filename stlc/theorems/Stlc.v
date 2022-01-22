From Coq Require Import List.
From Coq Require Import Program.Program.
(* Import coq-hammer for future proofs*)
From Hammer Require Import Hammer Tactics.

Require Import String.
Import ListNotations.

(* TODO: Implement well-typed errors *)
Definition error := string.

(* Define list function that searches through list and remove one matching element *)
Fixpoint removeMatch {A : Set} (p : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => if p x then xs else x :: removeMatch p xs
  end.

Inductive type : Set :=
  | TyBool : type
  | TyArrow : type -> type -> type.

Fixpoint type_eq (a:type) (b:type) : bool :=
  match (a, b) with
  | (TyBool, TyBool) => true
  | (TyArrow t11 t12, TyArrow t21 t22) => (type_eq t11 t21) && (type_eq t12 t22)
  | (_, _) => false
  end.

Example type_eq_test1 : type_eq TyBool TyBool = true.
Proof. reflexivity. Qed.

Example type_eq_test2 : type_eq TyBool (TyArrow TyBool TyBool) = false.
Proof. reflexivity. Qed.

Example type_eq_test3 : type_eq TyBool (TyArrow TyBool TyBool) = false.
Proof. reflexivity. Qed.

Example type_eq_test4 : type_eq (TyArrow TyBool (TyArrow TyBool TyBool))
                                (TyArrow TyBool (TyArrow TyBool TyBool)) = true.
Proof. reflexivity. Qed.

Inductive term : Set :=
   | TmTrue : term
   | TmFalse : term
   | TmIf : term -> term -> term -> term
   | TmVar : string -> term
   | TmAbs : string -> type -> term -> term
   | TmApp : term -> term -> term.

Inductive bind_kind : Set :=
  | BindName : bind_kind
  | BindVar : type -> bind_kind.

Record binding : Set := binding_mk { bind_name : string ; kind : bind_kind }.

Record context : Set := context_mk { bindings : list binding }.

Definition empty_context := context_mk [].

Definition add_binding (ctx : context) (name : string) (bind : bind_kind) : context :=
  context_mk (binding_mk name bind :: ctx.(bindings)).

Definition get_binding (ctx : context) (name : string) : error + bind_kind :=
  match option_map (fun b => b.(kind)) (List.find (fun b => eqb b.(bind_name) name) ctx.(bindings)) with
  | Some bk => inr bk
  | None => inl ("get_binding: Wrong kind of binding for variable `" ++ name ++ "`")%string
  end.

Definition get_type (ctx : context) (name : string) : error + type :=
  match get_binding ctx name with
  | inr (BindVar tyT) => inr tyT
  | inr _ => inl ("get_type: Wrong kind of binding for variable `" ++ name ++ "`")%string
  | inl e => inl e
  end.

Fixpoint type_of (ctx : context) (t : term) : error + type :=
  match t with
  | TmTrue
  | TmFalse => inr TyBool
  | TmIf t1 t2 t3 =>
    match (type_of ctx t1, type_of ctx t2, type_of ctx t3) with
    | (inr ty1, inr ty2, inr ty3) =>
      if type_eq ty1 TyBool then
        if type_eq ty2 ty3 then inr ty2
        else inl ("type_of: Arms of conditional have different types")%string
      else inl ("type_of: Guard of conditional expression not a boolean")%string
    | (inl e, _, _)
    | (_, inl e, _)
    | (_, _, inl e) => inl e
    end
  | TmVar name => get_type ctx name
  | TmAbs name tyT1 t2 =>
    let ctx' := add_binding ctx name (BindVar tyT1)
    in match type_of ctx' t2 with
    | inr tyT2 => inr (TyArrow tyT1 tyT2)
    | _ => inl ("type_of: Cannot find type for term")%string
    end
  | TmApp t1 t2 =>
    match (type_of ctx t1, type_of ctx t2) with
    | (inr ty1, inr ty2) =>
      match ty1 with
      | TyArrow ty11 ty12 =>
        if type_eq ty2 ty11 then inr ty12
        else inl ("type_of: Parameter type mismatch")%string
      | _ => inl ("type_of: Arrow type expected")%string
      end
    | _ => inl ("type_of: Cannot find type for term")%string
    end
  end.

Example typeof_test1 : type_of (empty_context) TmTrue = inr TyBool.
Proof. reflexivity. Qed.

Example typeof_test2 : type_of (empty_context) TmFalse = inr TyBool.
Proof. reflexivity. Qed.

Example typeof_test3 : type_of (empty_context)
                                (TmIf (TmTrue)
                                      (TmTrue)
                                      (TmFalse))
                        = inr TyBool.
Proof. reflexivity. Qed.

Example typeof_test4 :type_of (empty_context)
                              (TmAbs "f" TyBool (TmAbs "f'" TyBool TmTrue))
                      = inr (TyArrow TyBool (TyArrow TyBool TyBool)).
Proof. reflexivity. Qed.

Example typeof_test5 : type_of (empty_context) (TmApp (TmAbs "f" TyBool TmTrue) TmFalse)
                        = inr TyBool.
Proof. reflexivity. Qed.

Compute type_of (context_mk [binding_mk "f" (BindVar (TyArrow TyBool TyBool))]) (TmVar "f").
Example typeof_test6 : type_of (context_mk [binding_mk "f" (BindVar (TyArrow TyBool TyBool))])
                                (TmIf (TmTrue)
                                      (TmApp (TmVar "f") TmTrue)
                                      (TmFalse))%string
                        = inr TyBool.
Proof. reflexivity. Qed.

(* Theorem abs_type : forall (name : string) (ty : type) (tm : term) (ctx: context), *)
(*                      type_of ctx (TmAbs name ty tm) *)
(*                    = TyArrow ty (type_of (add_binding ctx name (BindVar ty)) tm). *)

(* TODO: Split term to safe and unsafe for reduction *)
(* Record well_typed_term : Set := mk_typed_term { tt_term : term ; tt_type : type }. *)

(* Fixpoint reduce (ctx: context) (t : term) : error + term := *)
(*   match t with *)
(*   | TmTrue => inr TmTrue *)
(*   | TmFalse => inr TmFalse *)
(*   | TmIf t₁ t₂ t₃ => *)
(*   | TmVar name => get_type ctx name *)
(*   | TmAbs name tyT₁ t₂ => *)
(*   | TmApp t₁ t₂ => *)
(*   end. *)
