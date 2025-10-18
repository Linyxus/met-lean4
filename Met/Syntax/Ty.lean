import Met.Syntax.Effect
namespace Met

inductive Ty : Type where
| unit : Ty
| arrow : Ty -> Ty -> Ty
| boxed : Modality -> Ty -> Ty

inductive Kind : Type where
| abs : Kind
| any : Kind

end Met
