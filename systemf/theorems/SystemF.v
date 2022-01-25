From Coq Require Import List.
From Coq Require Import Program.Program.

Require Import String.
Import ListNotations.

Definition error := string.

(* Define list function that searches through list and remove one matching element *)
Fixpoint removeMatch {A : Set} (p : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x::xs => if p x then xs else x :: removeMatch p xs
  end.

Inductive type : Set :=
  | TyBool : type
  | TyNat : type
  | TyPair : type -> type -> type
  | TyArrow : type -> type -> type
  | TyForall : string -> type -> type
  | TyVar : string -> type.
  (* | TyExists : string -> type -> type. *)

Fixpoint type_eq (a : type) (b : type) : bool :=
  match (a, b) with
  | (TyBool, TyBool)
  | (TyNat, TyNat) => true
  | (TyPair t11 t12, TyPair t21 t22)
  | (TyArrow t11 t12, TyArrow t21 t22) => (type_eq t11 t21) && (type_eq t12 t22)
  | (TyForall n1 t1, TyForall n2 t2) => (type_eq t1 t2) && (eqb n1 n2)
  | (TyVar n1, TyVar n2) => eqb n1 n2
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

Example type_eq_test5 : type_eq (TyForall "α" (TyArrow TyBool TyBool))
                                (TyArrow TyBool (TyArrow TyBool TyBool)) = false.
Proof. reflexivity. Qed.

Example type_eq_test6 : type_eq (TyForall "α" (TyArrow (TyVar "α") TyBool))
                                (TyForall "α" (TyArrow (TyVar "α") TyBool)) = true.
Proof. reflexivity. Qed.

Definition type_eq_decidable : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. all: apply string_dec.
Defined.

Fixpoint replace_typevar (t : type) (n : string) (t' : type) : type :=
  match t with
  | TyVar name => if eqb name n then t' else TyVar name
  | TyPair t1 t2 => TyPair (replace_typevar t1 n t') (replace_typevar t2 n t')
  | TyArrow t1 t2 => TyArrow (replace_typevar t1 n t') (replace_typevar t2 n t')
  | t'' => t''
  end.

Compute replace_typevar (TyArrow (TyVar "α") (TyVar "α")) "α" TyBool.

Example replace_typevar_test1 : replace_typevar (TyVar "α") "α" TyNat
                              = TyNat.
Proof. reflexivity. Qed.

Example replace_typevar_test2 : replace_typevar (TyArrow (TyVar "α") (TyVar "α")) "α" (TyVar "β")
                              = TyArrow (TyVar "β") (TyVar "β").
Proof. reflexivity. Qed.

Example replace_typevar_test3 : replace_typevar (TyArrow (TyVar "α") (TyVar "α")) "α" TyBool
                              = TyArrow TyBool TyBool.
Proof. reflexivity. Qed.

Inductive term : Set :=
  | TmTrue : term
  | TmFalse : term
  | TmNot : term -> term
  | TmAnd : term -> term -> term
  | TmOr : term -> term -> term
  | TmIf : term -> term -> term -> term

  | TmZero : term
  | TmSucc : term -> term
  | TmPred : term -> term

  | TmMkPair : term -> term -> term
  | TmFst : term -> term
  | TmSnd : term -> term

  | TmVar : string -> term
  | TmAbs : string -> type -> term -> term
  | TmApp : term -> term -> term

  | TmTyAbs : string -> term -> term
  | TmTyApp : term -> type -> term.

Inductive bind_kind : Set :=
  | BindVar : type -> bind_kind
  | BindTyVar : bind_kind.

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
  | inr BindTyVar => inr (TyVar name)
  | inl e => inl e
  end.

Fixpoint type_of (ctx : context) (t : term) : error + type :=
  match t with
  | TmTrue
  | TmFalse => inr TyBool
  | TmNot t =>
    match type_of ctx t with
    | inr TyBool => inr TyBool
    | inr _ => inl ("type_of: Expected term of type boolean")%string
    | inl e => inl e
    end
  | TmAnd t1 t2
  | TmOr t1 t2 =>
    match (type_of ctx t1, type_of ctx t2) with
    | (inr TyBool, inr TyBool) => inr TyBool
    (* TODO: Split in three cases for better error msg's *)
    | (inr TyBool, inr _) =>
      inl ("type_of: Expected term of type boolean on the right side of operator")%string
    | (inr _, inr TyBool) =>
      inl ("type_of: Expected term of type boolean on the left side of operator")%string
    | (inr _, inr _) =>
      inl ("type_of: Expected terms of type boolean")%string
    | (inl e, _)
    | (_, inl e) => inl e
    end
  | TmIf t1 t2 t3 =>
    match (type_of ctx t1, type_of ctx t2, type_of ctx t3) with
    | (inr TyBool, inr ty1, inr ty2) =>
      if type_eq ty1 ty2 then inr ty1
      else inl ("type_of: Arms of conditional have different types")%string
    | (inr _, inr _, inr _) =>
      inl ("type_of: Guard of conditional expression not a boolean")%string
    | (inl e, _, _)
    | (_, inl e, _)
    | (_, _, inl e) => inl e
    end

  | TmZero => inr TyNat
  | TmSucc t
  | TmPred t =>
    match type_of ctx t with
    | inr TyNat => inr TyNat
    (* TODO: Print received type *)
    | inr _ => inl ("type_of: Expected term of type nat")%string
    | inl e => inl e
    end

  | TmMkPair t1 t2 =>
    match (type_of ctx t1, type_of ctx t2) with
    | (inr ty1, inr ty2) => inr (TyPair ty1 ty2)
    | (inl e, _)
    | (_, inl e) => inl e
    end
  | TmFst p =>
    match type_of ctx p with
    | inr (TyPair ty1 ty2) => inr ty1
    (* TODO: Print received type *)
    | inr _ => inl ("type_of: Expected term of type pair")%string
    | inl e => inl e
    end
  | TmSnd p =>
    match type_of ctx p with
    | inr (TyPair ty1 ty2) => inr ty2
    (* TODO: Print received type *)
    | inr _ => inl ("type_of: Expected term of type pair")%string
    | inl e => inl e
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

  | TmTyAbs name t =>
    let ctx' := add_binding ctx name BindTyVar
    in match type_of ctx' t with
    | inr ty2 => inr (TyForall name ty2)
    | _ => inl ("type_of: Cannot find type for term")%string
    end
  (* XXX: Possibly wrong implementation *)
  | TmTyApp t ty =>
    match type_of ctx t with
    | inr (TyForall name ty') =>
      match t with
      | TmTyAbs name' t' => match type_of (add_binding ctx name (BindVar ty')) t' with
        | inr (t'') => inr (replace_typevar t'' name ty)
        | inl e => inl e
        end
      | _ => inl ("type_of: Expected universal type")%string
      end
    | inr _ => inl ("type_of: Expected universal type")%string
    | inl e => inl e
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

Example typeof_test4 : type_of (empty_context)
                               (TmAbs "f" TyBool (TmAbs "f'" TyBool TmTrue))
                     = inr (TyArrow TyBool (TyArrow TyBool TyBool)).
Proof. reflexivity. Qed.

Example typeof_test5 : type_of (empty_context)
                               (TmApp (TmAbs "f" TyBool TmTrue) TmFalse)
                     = inr TyBool.
Proof. reflexivity. Qed.

Example typeof_test6 : type_of (context_mk
                                [binding_mk "f"
                                            (BindVar (TyArrow TyBool TyBool))])
                               (TmIf (TmTrue)
                                     (TmApp (TmVar "f") TmTrue)
                                     (TmFalse))
                     = inr TyBool.
Proof. reflexivity. Qed.


Example typeof_test7 : type_of (empty_context)
                               (TmTyAbs "α"
                                 (TmAbs "a" (TyVar "α")
                                        (TmVar "a")))%string
                     = inr (TyForall "α" (TyArrow (TyVar "α") (TyVar "α"))).
Proof. reflexivity. Qed.

Example typeof_test8 : type_of (empty_context)
                               (TmTyApp
                                (TmTyAbs "α"
                                  (TmAbs "a" (TyVar "α") (TmVar "a")))
                                  TyBool)%string
                     = inr (TyArrow TyBool TyBool).
Proof. reflexivity. Qed.
