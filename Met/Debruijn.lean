import Mathlib.Tactic
namespace Met

inductive BinderKind : Type where
| var : BinderKind

inductive Sig : Type where
| empty : Sig
| extend : Sig -> BinderKind -> Sig

namespace Sig

instance instEmptyCollection : EmptyCollection Sig where
  emptyCollection := Sig.empty

end Sig

postfix:65 ",x" => fun s => Sig.extend s BinderKind.var
infix:65 ",," => Sig.extend

inductive BVar : BinderKind -> Sig -> Type where
| here {s : Sig} {k : BinderKind} :
  BVar k (s,,k)
| there :
  BVar k s ->
  BVar k (s,,k0)

end Met
