import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.GroupTheory.GroupAction.Defs

class Module' (R : Type*) [Semiring R] (M : Type*) where
  isAddCommMonoid : AddCommMonoid M
  isDistribMulAction : DistribMulAction R M
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : M, (0 : R) • x = 0

open CategoryTheory
def ModuleCat' (R : Type u) [Semiring R] := Bundled (Module' R)

#check Module
variable (R : Type u) [Semiring R]
#check Module R
