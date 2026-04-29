import LinearAlgebraInLean.Group

def nonzeros (r: Group R op)  := {x : R // x ≠ Group.neutral op}

class Field (R : Type) (add: operation R) where
  addStructure : AbelianGroup R add
  mul : operation addStructure.nonzeros
  mulStructure : AbelianGroup addStructure.nonzeros mul

instance [x: AbelianGroup Rat Rat.add] : Field Rat (Rat.add) where
  addStructure := x
  mul := Rat.mul

def zero_devisor_free (a b z : S) (op: operation S) := a = z ∨ b = z ↔ op a b = z
#check Rat.mul_eq_zero
#check Rat
