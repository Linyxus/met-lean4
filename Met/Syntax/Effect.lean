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

inductive EffExtension : Type where
| nil : EffExtension
| cons : EffLabel -> EffExtension -> EffExtension

namespace EffExtension

instance instEmptyCollection : EmptyCollection EffExtension where
  emptyCollection := EffExtension.nil

end EffExtension

inductive Modality : Type where
| abs : EffCtx -> Modality
| rel : EffExtension -> Modality

end Met
