import Met.Syntax.Ty
import Met.Debruijn
namespace Met

inductive ExpKind : Type where
| value : ExpKind
| term : ExpKind

inductive Exp : ExpKind -> Sig -> Type where
| unit : Exp .value s

end Met
