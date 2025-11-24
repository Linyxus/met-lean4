namespace Met

def EffLabel : Type := Nat

instance EffLabel.instInhabited : Inhabited EffLabel where
  default := (0 : Nat)

instance EffLabel.instDecidableEq : DecidableEq EffLabel :=
  fun l1 l2 => by unfold EffLabel at *; infer_instance

inductive EffCtx : Type where
| empty : EffCtx
| cons : EffLabel -> EffCtx -> EffCtx

namespace EffCtx

instance instEmptyCollection : EmptyCollection EffCtx where
  emptyCollection := EffCtx.empty

end EffCtx

/-- Effect extensions D ::= · | ℓ, D -/
inductive EffExtension : Type where
| nil : EffExtension
| cons : EffLabel -> EffExtension -> EffExtension

namespace EffExtension

instance instEmptyCollection : EmptyCollection EffExtension where
  emptyCollection := EffExtension.nil

end EffExtension

/-- Masks L ::= · | ℓ, L (multisets of labels) -/
abbrev Mask := EffExtension

/-- Modalities μ, ν ::= [E] | ⟨L|D⟩
    - Absolute modality [E] replaces the effect context with E
    - Relative modality ⟨L|D⟩ masks labels L and extends with D -/
inductive Modality : Type where
| abs : EffCtx -> Modality
| rel : Mask -> EffExtension -> Modality

namespace Modality

/-- The identity modality ⟨⟩ = ⟨·|·⟩ -/
def identity : Modality := rel EffExtension.nil EffExtension.nil

end Modality

/-- Concrete modality -/
structure CMod : Type where
  ctx : EffCtx
  mod : Modality

/-! ## Effect Operations -/

namespace EffExtension

/-- Check if a label is in an extension/mask -/
def contains : EffExtension → EffLabel → Bool
| .nil, _ => false
| .cons l m, l' => l == l' || contains m l'

/-- Remove a label from an extension/mask (removes first occurrence) -/
def remove : EffExtension → EffLabel → EffExtension
| .nil, _ => .nil
| .cons l m, l' => if l == l' then m else .cons l (remove m l')

/-- Concatenate two extensions -/
def append : EffExtension → EffExtension → EffExtension
| .nil, m => m
| .cons l e, m => .cons l (append e m)

instance : Append EffExtension where
  append := append

/-- D + E: Extend effect context E with extension D (D is prepended) -/
def extendCtx : EffExtension → EffCtx → EffCtx
| .nil, e => e
| .cons l d, e => .cons l (extendCtx d e)

end EffExtension

infixl:65 " +ₑ " => EffExtension.extendCtx

namespace EffCtx

/-- E - L: Remove labels in mask L from effect context E -/
def mask : EffCtx → Mask → EffCtx
| .empty, _ => .empty
| .cons l e, m =>
    if m.contains l then mask e (m.remove l)
    else .cons l (mask e m)

end EffCtx

infixl:65 " -ₑ " => EffCtx.mask

namespace Mask

/-- L ⊲⊳ D: Compute the difference between mask L and extension D
    Returns (L', D') where:
    - L' contains labels in L that are not in D
    - D' contains entries in D whose labels are not in L -/
def diff : Mask → EffExtension → Mask × EffExtension
| l, .nil => (l, .nil)
| l, .cons lbl d =>
    let (l', d') := diff l d
    if l.contains lbl then (l'.remove lbl, d')
    else (l', .cons lbl d')

end Mask

infixl:65 " ⊲⊳ " => Mask.diff

namespace Modality

/-- Apply a modality to an effect context
    [E](F) = E
    ⟨L|D⟩(F) = D + (F - L) -/
def apply : Modality → EffCtx → EffCtx
| .abs e, _ => e
| .rel l d, f => d +ₑ (f -ₑ l)

/-- Compose two modalities (reads left to right)
    μ ∘ [E] = [E]
    [E] ∘ ⟨L|D⟩ = [D + (E - L)]
    ⟨L₁|D₁⟩ ∘ ⟨L₂|D₂⟩ = ⟨L₁ + L|D₂ + D⟩ where (L, D) = L₂ ⊲⊳ D₁ -/
def comp : Modality → Modality → Modality
| _, .abs e => .abs e
| .abs e, .rel l d => .abs (d +ₑ (e -ₑ l))
| .rel l1 d1, .rel l2 d2 =>
    let (l, d) := l2 ⊲⊳ d1
    .rel (l1 ++ l) (d2 ++ d)

end Modality

infixl:65 " ∘ₘ " => Modality.comp

namespace CMod

/-- The source effect context of a concrete modality -/
def source (cm : CMod) : EffCtx := cm.mod.apply cm.ctx

/-- Check if μ_F : E → F (i.e., μ(F) = E) -/
def maps (cm : CMod) (e : EffCtx) : Prop := cm.source = e

/-- Compose two concrete modalities:
    μ_F ∘ ν_E : E' → F where ν_E : E' → E and μ_F : E → F -/
def comp (cm1 : CMod) (cm2 : CMod) : CMod :=
  { ctx := cm1.ctx, mod := cm1.mod ∘ₘ cm2.mod }

end CMod

/-! ## Sub-effecting and Effect Context Relations -/

namespace EffCtx

/-- Check if label ℓ is present in effect context E -/
def hasLabel : EffCtx → EffLabel → Bool
| .empty, _ => false
| .cons l e, l' => l == l' || hasLabel e l'

/-- Get the head label of a non-empty effect context -/
def head? : EffCtx → Option EffLabel
| .empty => none
| .cons l _ => some l

/-- Get the tail of an effect context -/
def tail : EffCtx → EffCtx
| .empty => .empty
| .cons _ e => e

end EffCtx

namespace EffExtension

/-- Get domain labels of an extension -/
def labels : EffExtension → List EffLabel
| .nil => []
| .cons l e => l :: labels e

/-- Check if extension has a label -/
def hasLabel : EffExtension → EffLabel → Bool
| .nil, _ => false
| .cons l e, l' => l == l' || hasLabel e l'

end EffExtension

/-! ## Modality Transformations

The transformation relation μ_F ⇒ ν_F is defined inductively by the following rules:
- MT-Abs: [E]_F ⇒ μ_F when E ⊆ μ(F)
- MT-Expand: ⟨L|D⟩_F ⇒ ⟨ℓ,L|ℓ,D⟩_F when ℓ ∈ (F - L)
- MT-Shrink: ⟨ℓ,L|ℓ,D⟩_F ⇒ ⟨L|D⟩_F when ℓ ∈ (F - L)
-/

/-- Modality transformation relation μ_F ⇒ ν_F
    This is the transitive closure of the base transformation rules -/
inductive ModTrans : CMod → CMod → Prop where
  /-- Reflexivity -/
  | refl : ModTrans cm cm
  /-- Transitivity -/
  | trans : ModTrans cm1 cm2 → ModTrans cm2 cm3 → ModTrans cm1 cm3
  /-- MT-Abs: An absolute modality can be transformed to any modality
      as long as no effects are lost. [E]_F ⇒ μ_F when E ≤ μ(F) -/
  | abs {f e μ} :
    ModTrans ⟨f, .abs e⟩ ⟨f, μ⟩
  /-- MT-Expand: Simultaneously mask and extend with an operation
      that exists in the ambient context.
      ⟨L|D⟩_F ⇒ ⟨ℓ,L|ℓ,D⟩_F when ℓ ∈ (F - L) -/
  | expand {f l d lbl} :
    (f -ₑ l).hasLabel lbl →
    ModTrans ⟨f, .rel l d⟩ ⟨f, .rel (.cons lbl l) (.cons lbl d)⟩
  /-- MT-Shrink: Remove a masked and extended label.
      ⟨ℓ,L|ℓ,D⟩_F ⇒ ⟨L|D⟩_F when ℓ ∈ (F - L) -/
  | shrink {f l d lbl} :
    (f -ₑ l).hasLabel lbl →
    ModTrans ⟨f, .rel (.cons lbl l) (.cons lbl d)⟩ ⟨f, .rel l d⟩

infix:50 " ⇒ₘ " => ModTrans

end Met
