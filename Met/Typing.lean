import Met.Substitution
namespace Met

/-! # Typing Contexts

The typing context Γ in Met consists of:
- Variable bindings with modality annotations: Γ, x :_{μ_F} A
- Locks: Γ, 🔒_{μ_F}

We use de Bruijn indices, so the context is a list of entries.
-/

/-- An entry in the typing context -/
inductive CtxEntry : Type where
  /-- Variable binding with a type and concrete modality -/
  | var : Ty → CMod → CtxEntry
  /-- Lock with a concrete modality -/
  | lock : CMod → CtxEntry

/-- A typing context is a list of entries -/
abbrev TyCtx := List CtxEntry

namespace TyCtx

/-- The empty context -/
def empty : TyCtx := []

/-- Extend the context with a variable binding -/
def extendVar (Γ : TyCtx) (A : Ty) (μ : CMod) : TyCtx :=
  .var A μ :: Γ

/-- Extend the context with a lock -/
def extendLock (Γ : TyCtx) (μ : CMod) : TyCtx :=
  .lock μ :: Γ

/-- Compute locks(Γ'): compose all modalities on locks in a context suffix Γ' -/
def locks : TyCtx → Modality
| [] => Modality.identity
| .var _ _ :: Γ => locks Γ
| .lock μ :: Γ => locks Γ ∘ₘ μ.mod

/-- Get the type and modality at a given de Bruijn index -/
def lookup : TyCtx → Nat → Option (Ty × CMod)
| [], _ => none
| .var A μ :: _, 0 => some (A, μ)
| .var _ _ :: Γ, n + 1 => lookup Γ n
| .lock _ :: Γ, n => lookup Γ n

/-- Get the suffix of the context after a given index (used for computing locks) -/
def suffix : TyCtx → Nat → TyCtx
| [], _ => []
| .var _ _ :: Γ, 0 => Γ
| .var _ _ :: Γ, n + 1 => suffix Γ n
| .lock μ :: Γ, n => .lock μ :: suffix Γ n

/-- Compute locks for the suffix after index n -/
def locksAfter (Γ : TyCtx) (n : Nat) : Modality :=
  locks (suffix Γ n)

end TyCtx

/-! ## Context Well-formedness

A context Γ is well-formed at effect context E, written Γ @ E.
-/

/-- Well-formedness of a context at an effect context -/
inductive CtxWf : TyCtx → EffCtx → Prop where
  /-- Empty context is well-formed at any effect context -/
  | empty : CtxWf [] E
  /-- Extending with a variable preserves well-formedness
      if the modality maps F to E -/
  | var {Γ F A} (μ : Modality) (E : EffCtx) :
    CtxWf Γ F →
    μ.apply F = E →
    CtxWf (TyCtx.extendVar Γ A ⟨F, μ⟩) F
  /-- Extending with a lock changes the effect context -/
  | lock {Γ F} (μ : Modality) (E : EffCtx) :
    CtxWf Γ F →
    μ.apply F = E →
    CtxWf (TyCtx.extendLock Γ ⟨F, μ⟩) E

/-- Notation for context well-formedness -/
scoped notation:50 Γ " @ₑ " E => CtxWf Γ E

/-! ## Kinding

The kinding judgment Γ ⊢ A : K determines the kind of a type.
- Abs: Types whose values are independent of the effect context
- Any: All types

Key rules:
- Unit type has kind Abs
- Boxed types with absolute modality [E] have kind Abs
- Boxed types with relative modality ⟨L|D⟩ preserve the kind
- Function types have kind Any
-/

/-- Kinding judgment -/
inductive HasKind : Ty → Kind → Prop where
  /-- Unit type has kind Abs -/
  | unit : HasKind .unit .abs
  /-- Subkinding: Abs is a subkind of Any -/
  | sub : HasKind A .abs → HasKind A .any
  /-- Absolute modality produces Abs kind -/
  | boxedAbs {E A} : HasKind A .any → HasKind (.boxed (.abs E) A) .abs
  /-- Relative modality preserves kind -/
  | boxedRel {L D A K} : HasKind A K → HasKind (.boxed (.rel L D) A) K
  /-- Function types have kind Any -/
  | arrow {A B} : HasKind A .any → HasKind B .any → HasKind (.arrow A B) .any

/-- Check if a type is absolute (has kind Abs) -/
def Ty.isAbs : Ty → Bool
| .unit => true
| .boxed (.abs _) _ => true
| .boxed (.rel _ _) A => A.isAbs
| .arrow _ _ => false

/-! ## Auxiliary Judgments for Typing -/

/-- The judgment Γ ⊢ (μ, A) ⇒ ν @ F
    Used in T-Var to check if a variable can be accessed.
    - If A is absolute, the variable can always be accessed
    - Otherwise, we need μ_F ⇒ ν_F -/
inductive VarAccessible : TyCtx → Modality → Ty → Modality → EffCtx → Prop where
  /-- Absolute types can always be accessed -/
  | abs {Γ μ A ν F} : HasKind A .abs → VarAccessible Γ μ A ν F
  /-- Non-absolute types require a modality transformation -/
  | trans {Γ μ A ν F} : ⟨F, μ⟩ ⇒ₘ ⟨F, ν⟩ → VarAccessible Γ μ A ν F

/-! ## Typing Judgment

The typing judgment Γ ⊢ M : A @ E
-/

/-- Convert a de Bruijn variable to a natural number index -/
def BVar.toNat : BVar k s → Nat
| .here => 0
| .there x => x.toNat + 1

mutual

/-- Typing for effect clauses in a handler.
    Each clause for operation ℓ : A ↠ B' is typed with:
    - p : A (parameter)
    - r : B' → B (continuation, where B is handler result type)
    The body should have type B at effect context F. -/
inductive ClausesTyped : TyCtx → EffClauses k s → Ty → EffCtx → Prop where
  /-- Empty clauses are well-typed -/
  | nil {Γ k s B F} : ClausesTyped Γ (.nil : EffClauses k s) B F
  /-- A clause for operation ℓ : A ↠ B' is well-typed if
      the body is typed with p : A and r : B' → B -/
  | cons {Γ s k A B' B F} {body : Exp k ((s,x),x)} {cls : EffClauses k s}
      (ℓ : EffLabel) :
    Typed (TyCtx.extendVar
            (TyCtx.extendVar Γ A ⟨F, .identity⟩)
            (.arrow B' B) ⟨F, .identity⟩) body B F →
    ClausesTyped Γ cls B F →
    ClausesTyped Γ (.cons ℓ body cls) B F

/-- Typing judgment: Γ ⊢ M : A @ E

The key typing rules are:
- T-Var: Variable access with modality transformation
- T-Mod: Modality introduction (boxing)
- T-Letmod: Modality elimination (unboxing)
- T-Abs: Lambda abstraction
- T-App: Application
- T-Do: Effect operation invocation
- T-Mask: Masking effects
- T-Handler: Handling effects
-/
inductive Typed : TyCtx → Exp k s → Ty → EffCtx → Prop where
  /-- T-Unit: Unit value -/
  | unit {Γ E} : Typed Γ .unit .unit E

  /-- T-Var: Variable access
      - ν_F = locks(Γ') : E → F
      - Γ ⊢ (μ, A) ⇒ ν @ F
      - Γ, x :_{μ_F} A, Γ' ⊢ x : A @ E -/
  | var {Γ s E A} {x : BVar .var s} (μ ν : Modality) (F : EffCtx) :
    TyCtx.lookup Γ x.toNat = some (A, ⟨F, μ⟩) →
    TyCtx.locksAfter Γ x.toNat = ν →
    ν.apply F = E →
    VarAccessible Γ μ A ν F →
    Typed Γ (.var x) A E

  /-- T-Abs: Lambda abstraction
      Γ, x : A ⊢ M : B @ E
      ─────────────────────
      Γ ⊢ λx.M : A → B @ E -/
  | lam {Γ s E A B k} {M : Exp k (s,x)} :
    Typed (TyCtx.extendVar Γ A ⟨E, .identity⟩) M B E →
    Typed Γ (.lam A M) (.arrow A B) E

  /-- T-App: Application
      Γ ⊢ M : A → B @ E    Γ ⊢ N : A @ E
      ───────────────────────────────────
      Γ ⊢ M N : B @ E -/
  | app {Γ s E A B k1 k2} {M : Exp k1 s} {N : Exp k2 s} :
    Typed Γ M (.arrow A B) E →
    Typed Γ N A E →
    Typed Γ (.app M N) B E

  /-- T-Mod: Modality introduction (boxing)
      μ_F : E → F    Γ, 🔒_{μ_F} ⊢ V : A @ E
      ──────────────────────────────────────
      Γ ⊢ mod_μ V : μA @ F -/
  | mod {Γ s F A} {V : Exp .value s} (μ : Modality) (E : EffCtx) :
    μ.apply F = E →
    Typed (TyCtx.extendLock Γ ⟨F, μ⟩) V A E →
    Typed Γ (.mod μ V) (.boxed μ A) F

  /-- T-Letmod: Modality elimination (unboxing)
      ν_F : E → F    Γ, 🔒_{ν_F} ⊢ V : μA @ E
      Γ, x :_{ν_F ∘ μ_E} A ⊢ M : B @ F
      ─────────────────────────────────────────
      Γ ⊢ let_ν mod_μ x = V in M : B @ F -/
  | letmod {Γ s F A B k} {V : Exp .value s} {M : Exp k (s,x)}
      (ν μ : Modality) (E : EffCtx) :
    ν.apply F = E →
    Typed (TyCtx.extendLock Γ ⟨F, ν⟩) V (.boxed μ A) E →
    Typed (TyCtx.extendVar Γ A ⟨F, ν ∘ₘ μ⟩) M B F →
    Typed Γ (.letmod ν μ V M) B F

  /-- T-Do: Effect operation invocation
      E = ℓ : A ↠ B, F    Γ ⊢ N : A @ E
      ─────────────────────────────────
      Γ ⊢ do ℓ N : B @ E -/
  | effdo {Γ s E A B k} {N : Exp k s} (ℓ : EffLabel) (F : EffCtx) :
    E = .cons ℓ F →
    Typed Γ N A E →
    Typed Γ (.effdo ℓ N) B E

  /-- T-Mask: Masking effects
      Γ, 🔒_{⟨L|·⟩_F} ⊢ M : A @ F - L
      ──────────────────────────────
      Γ ⊢ mask_L M : ⟨L|·⟩A @ F -/
  | mask {Γ s F A k} {M : Exp k s} (L : Mask) :
    Typed (TyCtx.extendLock Γ ⟨F, .rel L .nil⟩) M A (F -ₑ L) →
    Typed Γ (.mask L M) (.boxed (.rel L .nil) A) F

  /-- T-Handler: Handling effects
      H = {return x ↦→ N} ⊎ {ℓᵢ pᵢ rᵢ ↦→ Nᵢ}ᵢ
      Γ, 🔒_{⟨|D⟩_F} ⊢ M : A @ D + F
      Γ, x : ⟨|D⟩A ⊢ N : B @ F
      D = {ℓᵢ : Aᵢ ↠ Bᵢ}ᵢ
      [Γ, pᵢ : Aᵢ, rᵢ : Bᵢ → B ⊢ Nᵢ : B @ F]ᵢ
      ─────────────────────────────────────────
      Γ ⊢ handle M with H : B @ F -/
  | handle {Γ s F A B k} {M : Exp k s} {H : Handler k s} (D : EffExtension) :
    H.eff = D →
    Typed (TyCtx.extendLock Γ ⟨F, .rel .nil D⟩) M A (D +ₑ F) →
    Typed (TyCtx.extendVar Γ (.boxed (.rel .nil D) A) ⟨F, .identity⟩) H.retBody B F →
    ClausesTyped Γ H.clauses B F →
    Typed Γ (.handle M H) B F

end

end Met
