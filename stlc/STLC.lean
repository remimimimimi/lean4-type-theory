import Std.Data.AssocList
open Std

inductive TType : Type where
  | bool : TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, DecidableEq

inductive Term : Type where
  | true : Term
  | false : Term
  | var : String → Term
  | tif : Term → Term → Term → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term
  deriving Repr

inductive WTTerm : TType → Type where
  | true : WTTerm .bool
  | false : WTTerm .bool
  | var : ∀ t, String → WTTerm t
  | tif : ∀ t, (cond : WTTerm .bool) → (tb : WTTerm t) → (fb : WTTerm t) → WTTerm t
  | abs : ∀ t₂, (name : String) → (t₁ : TType) → (body : WTTerm t) → WTTerm (.arrow t₁ t₂)
  | app : ∀ t₁ t₂, WTTerm (.arrow t₁ t₂) → WTTerm t₁ → WTTerm t₂
  deriving Repr

def WTTerm.tmeq (tm₁ : WTTerm t₁) (tm₂ : WTTerm t₂) (eq : t₁ = t₂) : WTTerm t₂ := by
  rw [eq] at tm₁ <;> exact tm₁

def WTTerm.teq (tm₁ : WTTerm t₁) (_:TType) (eq : t₁ = t₂) : WTTerm t₂ := by
  rw [eq] at tm₁ <;> exact tm₁

inductive Maybe (p : α → Type) where
  | found : (a : α) → p a → Maybe p
  | unknown

def typecheck_aux : (tm : Term) → (ctx : AssocList String TType) → Maybe WTTerm
  | .true, ctx => .found .bool .true
  | .false, ctx => .found .bool .false
  | .var name, ctx =>
    match ctx.find? name with
    | some t => .found t (.var t name)
    | none => .unknown
  | .tif tm₁ tm₂ tm₃, ctx =>
    match typecheck_aux tm₁ ctx, typecheck_aux tm₂ ctx, typecheck_aux tm₃ ctx with
    | .found t₁ tm₁, .found t₂ tm₂, .found t₃ tm₃ =>
      match decEq t₁ .bool, decEq t₃ t₂ with
      | isTrue bprf, isTrue tprf =>
        .found t₂ (.tif t₂ (.teq tm₁ .bool bprf) tm₂ (.tmeq tm₃ tm₂ tprf))
      | _, _ => .unknown
    | _, _, _ => .unknown
  | .abs name t₁ tm₁, ctx₁ =>
    let ctx₂ := ctx₁.insert name t₁
    match typecheck_aux tm₁ ctx₂ with
    | .found t₂ tm₂ => .found (.arrow t₁ t₂) (.abs t₂ name t₁ tm₂)
    | .unknown => .unknown
  | .app tm₁ tm₂, ctx =>
    match typecheck_aux tm₁ ctx, typecheck_aux tm₂ ctx with
    | .found (.arrow t₁ t₂) tm₂₁, .found t₃ tm₂₂ =>
      match decEq t₃ t₁ with
      | isTrue prf =>
        .found t₂ <| .app t₂ t₁ tm₂₁ <| .teq tm₂₂ t₁ prf
      | _ => .unknown
    | _, _ => .unknown

def Term.typecheck (tm : Term) : Maybe WTTerm := typecheck_aux tm AssocList.empty
