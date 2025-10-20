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

def Rename (s1 s2 : Sig) : Type := ∀ {k}, BVar k s1 -> BVar k s2

def Rename.id : Rename s s := fun x => x

def Rename.comp (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 :=
  fun x => f2 (f1 x)

def BVar.rename {s1 s2 : Sig} (f : Rename s1 s2) {k : BinderKind}
  (x : BVar k s1) : BVar k s2 :=
  f x

def Rename.lift (f : Rename s1 s2) : Rename (s1,,k) (s2,,k) :=
  fun x =>
    match x with
    | BVar.here => BVar.here
    | BVar.there y => BVar.there (f y)

def Rename.succ : Rename s (s,,k) :=
  fun x => BVar.there x

end Met
