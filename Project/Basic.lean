import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Basic

class MulActionSemiModule (G R M : Type*)
    [Monoid G]
      [Semiring R] [MulSemiringAction G R]
        [AddCommMonoid M] [Module R M] [MulAction G M]
          where
  comp: ∀ g : G, ∀ r : R, ∀ m : M, g • (r • m) = (g • r) • (g • m)

class MulActionSemiModuleHom (G R R' M M': Type*)
    [Monoid G]
      [Semiring R] [MulSemiringAction G R]
        [Semiring R'] [MulSemiringAction G R']
          [AddCommMonoid M] [Module R M] [MulAction G M] [MulActionSemiModule G R M]
            [AddCommMonoid M'] [Module R' M'] [MulAction G M'] [MulActionSemiModule G R' M']
              where
  -- comp: ∀ g : G, ∀ r : R, ∀ m : M, g • (r • m) = (g • r) • (g • m)

class ContinuousMulAction (M S : Type*)
  [Monoid M] [TopologicalSpace M] [ContinuousMul M] [TopologicalSpace S]
    extends MulAction M S, ContinuousSMul M S where

class ContinuousMulSemiringAction (M R : Type*)
  [Monoid M] [TopologicalSpace M] [ContinuousMul M] [TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
    extends MulAction M R, ContinuousSMul M R where

-- class Module' (R : Type*) [Semiring R] (M : Type*) where
--   isAddCommMonoid : AddCommMonoid M
--   isDistribMulAction : DistribMulAction R M
--   add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
--   zero_smul : ∀ x : M, (0 : R) • x = 0

-- open CategoryTheory
-- def ModuleCat' (R : Type u) [Semiring R] := Bundled (Module' R)

-- #check Module
-- variable (R : Type u) [Semiring R]
-- #check Module R
