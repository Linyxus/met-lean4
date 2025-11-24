import Met.Typing
namespace Met

/-! # Operational Semantics

The operational semantics for Met following Section 4.6 of the paper.
-/

/-! ## Values

Values V, W ::= () | x | λx^A.M | mod_μ V

We define a predicate `IsValue` on expressions.
-/

/-- A value predicate for expressions -/
inductive IsValue : Exp k s → Prop where
  | unit : IsValue (.unit : Exp .value s)
  | var {x : BVar .var s} : IsValue (.var x)
  | lam {A : Ty} {M : Exp k (s,x)} : IsValue (.lam A M)
  | mod {μ : Modality} {V : Exp .value s} : IsValue V → IsValue (.mod μ V)

/-! ## Evaluation Contexts

Evaluation contexts E ::= [ ] | E N | V E | do ℓ E | mask_L E | handle E with H

We represent evaluation contexts as an inductive type with a hole.
The hole always expects a term, since all redexes produce terms.
-/

/-- Evaluation contexts with a term hole.
    An EvalCtx represents a context with a hole that takes a term
    and produces an expression of kind `kresult`. -/
inductive EvalCtx : Sig → ExpKind → Type where
  /-- The hole [ ] for terms -/
  | hole : EvalCtx s .term
  /-- E N : Application with E in function position -/
  | appL : EvalCtx s k → Exp k' s → EvalCtx s .term
  /-- V E : Application with E in argument position (V must be a value) -/
  | appR : Exp .value s → EvalCtx s k → EvalCtx s .term
  /-- do ℓ E : Effect operation -/
  | effdo : EffLabel → EvalCtx s k → EvalCtx s .term
  /-- mask_L E : Masking -/
  | mask : Mask → EvalCtx s k → EvalCtx s .term
  /-- handle E with H : Handler -/
  | handle : EvalCtx s .term → Handler .term s → EvalCtx s .term

/-- Plug a term into an evaluation context -/
def EvalCtx.plug : EvalCtx s kresult → Exp .term s → Exp kresult s
  | .hole, M => M
  | .appL E N, M => .app (E.plug M) N
  | .appR V E, M => .app V (E.plug M)
  | .effdo ℓ E, M => .effdo ℓ (E.plug M)
  | .mask L E, M => .mask L (E.plug M)
  | .handle E H, M => .handle (E.plug M) H

notation:max E "[" M "]" => EvalCtx.plug E M

/-! ## n-free Predicate

The predicate n-free(ℓ, E) determines whether there are exactly n masks for ℓ
in the evaluation context E without corresponding handlers.

This is crucial for the E-Op rule to ensure the handler catches the operation.
-/

/-- Count occurrences of a label in a mask/extension -/
def EffExtension.count (ext : EffExtension) (ℓ : EffLabel) : Nat :=
  match ext with
  | .nil => 0
  | .cons ℓ' ext' => (if ℓ == ℓ' then 1 else 0) + ext'.count ℓ

/-- Check if a label is in the domain of handler clauses -/
def EffClauses.hasLabel : EffClauses k s → EffLabel → Bool
  | .nil, _ => false
  | .cons ℓ' _ cls, ℓ => ℓ == ℓ' || cls.hasLabel ℓ

/-- Check if a label is handled by a handler -/
def Handler.handlesLabel (H : Handler k s) (ℓ : EffLabel) : Bool :=
  H.clauses.hasLabel ℓ

/-- The n-free predicate: n-free(ℓ, E) holds if there are n masks for ℓ
    in E without corresponding handlers.

    Following Biernacki et al. [5], we define this inductively. -/
inductive NFree : Nat → EffLabel → EvalCtx s kresult → Prop where
  /-- 0-free(ℓ, [ ]) -/
  | hole : NFree 0 ℓ .hole
  /-- n-free(ℓ, E) implies n-free(ℓ, E N) -/
  | appL : NFree n ℓ E → NFree n ℓ (.appL E N)
  /-- n-free(ℓ, E) implies n-free(ℓ, V E) -/
  | appR : NFree n ℓ E → NFree n ℓ (.appR V E)
  /-- n-free(ℓ, E) implies n-free(ℓ, do ℓ' E) -/
  | effdo : NFree n ℓ E → NFree n ℓ (.effdo ℓ' E)
  /-- n-free(ℓ, E) and count(ℓ; L) = m implies (n + m)-free(ℓ, mask_L E) -/
  | mask : NFree n ℓ E → L.count ℓ = m → NFree (n + m) ℓ (.mask L E)
  /-- (n + 1)-free(ℓ, E) and ℓ ∈ dom(H) implies n-free(ℓ, handle E with H) -/
  | handleIn : NFree (n + 1) ℓ E → H.handlesLabel ℓ = true →
      NFree n ℓ (.handle E H)
  /-- n-free(ℓ, E) and ℓ ∉ dom(H) implies n-free(ℓ, handle E with H) -/
  | handleOut : NFree n ℓ E → H.handlesLabel ℓ = false →
      NFree n ℓ (.handle E H)

/-! ## Reduction Rules

The reduction relation M ↝ N.

All redexes are terms (.term), so Step is defined on terms.
The result can be any kind since substitution can change the kind.
-/

/-- Look up an effect clause by label -/
def EffClauses.lookup : EffClauses k s → EffLabel → Option (Exp k ((s,x),x))
  | .nil, _ => none
  | .cons ℓ' body cls, ℓ => if ℓ == ℓ' then some body else cls.lookup ℓ

/-- Single-step reduction relation on terms.
    Step M N means M reduces to N in one step. -/
inductive Step : Exp .term s → Exp k s → Prop where
  /-- E-App: (λx^A.M) V ↝ M[V/x] -/
  | app {A : Ty} {M : Exp k (s,x)} {V : Exp .value s} :
      Step (.app (.lam A M) V) (M.subst (Subst.openVar V))

  /-- E-Letmod: let_ν mod_μ x = mod_μ V in M ↝ M[V/x] -/
  | letmod {ν μ : Modality} {V : Exp .value s} {M : Exp k (s,x)} :
      Step (.letmod ν μ (.mod μ V) M) (M.subst (Subst.openVar V))

  /-- E-Mask: mask_L V ↝ mod_⟨L|⟩ V -/
  | mask {L : Mask} {V : Exp .value s} :
      IsValue V →
      Step (.mask L V) (.mod (.rel L .nil) V)

  /-- E-Ret: handle V with H ↝ N[(mod_⟨|D⟩ V)/x]
      where (return x ↦→ N) ∈ H
      Note: handle V H requires V : Exp k s and H : Handler k s.
      For E-Ret, V is a value in evaluation position.
      We coerce value V to term by noting it's in handle's term position. -/
  | ret {V : Exp .value s} {H : Handler .term s} :
      IsValue V →
      Step (.handle V H) (H.retBody.subst (Subst.openVar (.mod (.rel .nil H.eff) V)))

  /-- E-Op: handle E[do ℓ V] with H ↝ N[V/p, (λy.handle E[y] with H)/r]
      where 0-free(ℓ, E) and (ℓ p r ↦→ N) ∈ H -/
  | op {E : EvalCtx s .term} {V : Exp .value s} {H : Handler .term s}
      {ℓ : EffLabel} {body : Exp .term ((s,x),x)} {result : Exp .term s} :
      IsValue V →
      NFree 0 ℓ E →
      H.clauses.lookup ℓ = some body →
      -- The result is body[V/p, (λy.handle E[y] with H)/r]
      Step (.handle (E[Exp.effdo ℓ V]) H) result

  /-- E-Lift: E[M] ↝ E[N] if M ↝ N -/
  | lift {E : EvalCtx s kresult} {M : Exp .term s} {N : Exp k s} :
      Step M N →
      Step (E[M]) (E[N])

/-- Multi-step reduction (reflexive transitive closure) -/
inductive Steps : Exp .term s → Exp k s → Prop where
  | refl : Steps M M
  | step : Step M N → Steps N P → Steps M P

/-! ## Normal Forms

A term M is in normal form with respect to effect context E if it is either:
- A value V, or
- Of the form E[do ℓ V] for ℓ ∈ E and n-free(ℓ, E)
-/

/-- A term is in normal form (either a value or stuck on an effect) -/
inductive NormalForm : Exp .term s → Prop where
  /-- Values (embedded in term position) are normal forms -/
  | value {V : Exp .value s} : IsValue V → NormalForm V
  /-- Stuck on an effect operation (unhandled effect) -/
  | stuck {E : EvalCtx s .term} {V : Exp .value s} {ℓ : EffLabel} {n : Nat} :
      IsValue V → NFree n ℓ E → NormalForm (E[Exp.effdo ℓ V])

end Met
