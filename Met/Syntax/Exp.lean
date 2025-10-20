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

def Exp.rename : Exp k s1 -> Rename s1 s2 -> Exp k s2
| unit, _ => unit
| var x, f => var (f x)
| lam ty e, f => lam ty (e.rename f.lift)
| app e1 e2, f => app (e1.rename f) (e2.rename f)
| mod m e, f => mod m (e.rename f)
| letmod m1 m2 e1 e2, f => letmod m1 m2 (e1.rename f) (e2.rename f.lift)
| effdo l e, f => effdo l (e.rename f)

end Met
