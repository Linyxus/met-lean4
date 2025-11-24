import Met.Syntax.Ty
import Met.Debruijn
namespace Met

/-- Kinds of expressions. -/
inductive ExpKind : Type where
| value : ExpKind
| term : ExpKind

mutual

/-- Effect clauses in a handler: a list of (label, body) pairs
    Each body has two extra bound variables: p (parameter) and r (continuation)
    Note: We use a simple list structure with ExpKind parameter -/
inductive EffClauses : ExpKind → Sig → Type where
| nil : EffClauses k s
| cons : EffLabel → Exp k ((s,x),x) → EffClauses k s → EffClauses k s

/-- Handler H ::= {return x ↦→ M} ⊎ {ℓ p r ↦→ M}*
    - eff: the effects being handled
    - retBody: the return clause body (binds one var for return value)
    - clauses: the effect clauses -/
inductive Handler : ExpKind → Sig → Type where
| mk : EffExtension → Exp k (s,x) → EffClauses k s → Handler k s

/-- Expressions. -/
inductive Exp : ExpKind → Sig → Type where
| unit : Exp .value s
| var : BVar .var s → Exp .value s
| lam : Ty → Exp k (s,x) → Exp .value s
| app : Exp k1 s → Exp k2 s → Exp .term s
| mod : Modality → Exp .value s → Exp .value s
| letmod : Modality → Modality → Exp .value s → Exp k (s,x) → Exp .term s
| effdo : EffLabel → Exp k s → Exp .term s
| mask : Mask → Exp k s → Exp .term s
| handle : Exp k s → Handler k s → Exp .term s

end

namespace Handler

def eff : Handler k s → EffExtension
| .mk e _ _ => e

def retBody : Handler k s → Exp k (s,x)
| .mk _ r _ => r

def clauses : Handler k s → EffClauses k s
| .mk _ _ c => c

end Handler

mutual

def EffClauses.rename : EffClauses k s1 → Rename s1 s2 → EffClauses k s2
| .nil, _ => .nil
| .cons l e cs, f => .cons l (e.rename (Rename.lift (Rename.lift f))) (cs.rename f)

def Handler.rename : Handler k s1 → Rename s1 s2 → Handler k s2
| .mk eff ret cls, f => .mk eff (ret.rename (Rename.lift f)) (cls.rename f)

def Exp.rename : Exp k s1 → Rename s1 s2 → Exp k s2
| .unit, _ => .unit
| .var x, f => .var (f x)
| .lam ty e, f => .lam ty (e.rename (Rename.lift f))
| .app e1 e2, f => .app (e1.rename f) (e2.rename f)
| .mod m e, f => .mod m (e.rename f)
| .letmod m1 m2 e1 e2, f => .letmod m1 m2 (e1.rename f) (e2.rename (Rename.lift f))
| .effdo l e, f => .effdo l (e.rename f)
| .mask m e, f => .mask m (e.rename f)
| .handle e h, f => .handle (e.rename f) (h.rename f)

end

end Met
