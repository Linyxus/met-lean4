import Met.Syntax.Exp
namespace Met

/-- A substitution from signature `s1` to signature `s2`. -/
structure Subst (s1 s2 : Sig) : Type where
  var : ∀ {k}, BVar k s1 -> Exp .value s2

/-- Lift a substitution under a binder. -/
def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var x :=
    match x with
    | BVar.here => Exp.var BVar.here
    | BVar.there y => (σ.var y).rename Rename.succ

/-- The identity substitution that maps each variable to itself. -/
def Subst.id : Subst s s where
  var := fun x => Exp.var x

mutual

def EffClauses.subst : EffClauses k s1 → Subst s1 s2 → EffClauses k s2
| .nil, _ => .nil
| .cons l e cs, σ => .cons l (e.subst (Subst.lift (Subst.lift σ))) (cs.subst σ)

def Handler.subst : Handler k s1 → Subst s1 s2 → Handler k s2
| .mk eff ret cls, σ => .mk eff (ret.subst (Subst.lift σ)) (cls.subst σ)

def Exp.subst : Exp k s1 -> Subst s1 s2 -> Exp k s2
| .unit, _ => .unit
| .var x, σ => σ.var x
| .lam ty e, σ => .lam ty (e.subst (Subst.lift σ))
| .app e1 e2, σ => .app (e1.subst σ) (e2.subst σ)
| .mod m e, σ => .mod m (e.subst σ)
| .letmod m1 m2 e1 e2, σ => .letmod m1 m2 (e1.subst σ) (e2.subst (Subst.lift σ))
| .effdo l e, σ => .effdo l (e.subst σ)
| .mask m e, σ => .mask m (e.subst σ)
| .handle e h, σ => .handle (e.subst σ) (h.subst σ)

end

def Subst.openVar (v : Exp .value s) : Subst (s,x) s where
  var :=
    fun
    | BVar.here => v
    | BVar.there y => Exp.var y

end Met
