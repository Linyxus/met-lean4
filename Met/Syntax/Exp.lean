import Met.Syntax.Ty
import Met.Debruijn
namespace Met

/-- Kinds of expressions. -/
inductive ExpKind : Type where
| value : ExpKind
| term : ExpKind

/-- Expressions. -/
inductive Exp : ExpKind -> Sig -> Type where
| unit : Exp .value s
| var : BVar .var s -> Exp .value s
| lam : Ty -> Exp k (s,x) -> Exp .value s
| app : Exp k1 s -> Exp k2 s -> Exp .term s
| mod : Modality -> Exp .value s -> Exp .value s
| letmod : Modality -> Modality -> Exp .value s -> Exp k (s,x) -> Exp .term s
| effdo : EffLabel -> Exp k s -> Exp .term s

end Met
