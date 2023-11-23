import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RepresentationTheory.Action
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs

-- Fix a monoid `M`, how to constrcut the `Category` of semiring with an `M` action?
-- 1. Bundle a wrapper of `MulSemiringAction`
-- 2. `Action M Semiring`
-- We show they are equivalent.

-- TODO?: extend `MulSemiringActionHom` to change of groups?

open CategoryTheory

universe v u

variable (M : Type u) [Monoid M]

-- class MulSemiringAction' (carrier : Type v) where
--   [isSemiring : Semiring carrier]
--   [isMulSemiringAction : MulSemiringAction M carrier]

-- #check Bundled (MulSemiringAction' M)

structure MulSemiringActionCat where
  carrier : Type v
  [isSemiring : Semiring carrier]
  [isMulSemiringAction : MulSemiringAction M carrier]

attribute [instance] MulSemiringActionCat.isSemiring MulSemiringActionCat.isMulSemiringAction

instance : CoeSort (MulSemiringActionCat.{v} M) (Type v) :=
  ⟨MulSemiringActionCat.carrier⟩

attribute [coe] MulSemiringActionCat.carrier

instance mulSemiringActionCategory :
    Category.{v, max (v+1) u} (MulSemiringActionCat.{v} M) where
  Hom R S := MulSemiringActionHom M R S
  id _ := MulSemiringActionHom.id M
  comp f g := MulSemiringActionHom.comp g f
  -- id_comp := MulSemiringActionHom.id_comp
  -- comp_id := MulSemiringActionHom.comp_id
  -- assoc f g h := sorry

instance {R S : MulSemiringActionCat.{v} M} :
    MulSemiringActionHomClass (R ⟶ S) M R S :=
  MulSemiringActionHom.instMulSemiringActionHomClassMulSemiringActionHomToDistribMulActionToDistribMulAction M R S
-- This naming is abhorrent

instance moduleConcreteCategory :
    ConcreteCategory.{v} (MulSemiringActionCat.{v} M) where
  forget := {
    obj := fun R => R
    map := fun f => f.toFun
  }
  forget_faithful := {
    map_injective := by
      intro R S f g h
      apply MulSemiringActionHom.ext
      exact congrFun h
  }
    -- ⟨fun h => MulSemiringActionHom.ext (fun x => by
    --   dsimp at h
    --   rw [h])⟩
-- why different proof for module?

instance {R : MulSemiringActionCat.{v} M} :
    Semiring ((forget (MulSemiringActionCat M)).obj R) :=
  (inferInstance : Semiring R)

instance {R : MulSemiringActionCat.{v} M} :
    MulSemiringAction M ((forget (MulSemiringActionCat M)).obj R) :=
  (inferInstance : MulSemiringAction M R)

@[ext]
lemma ext {R S : MulSemiringActionCat.{v} M} {f₁ f₂ : R ⟶ S} (h : ∀ (r : R), f₁ r = f₂ r) : f₁ = f₂ :=
  FunLike.ext _ _ h

instance hasForgetToSemiring : HasForget₂ (MulSemiringActionCat M) SemiRingCat where
  forget₂ := {
    obj := fun R => SemiRingCat.of R
    map := fun f => SemiRingCat.ofHom f.toRingHom
  }

-- Semiring or SemiRing????
def of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    MulSemiringActionCat M :=
  ⟨R⟩

/--
Forgeting an object in the action category to semiring category
is defeq to
the coesion to the underlying semiring in the semiring category
-/
@[simp]
theorem forget₂_obj (R : MulSemiringActionCat M) :
    (forget₂ (MulSemiringActionCat M) SemiRingCat).obj R = SemiRingCat.of R :=
  rfl

/--
Given the data of an actioned ring
assemble to the object in action category
then forget to semiring category
is defeq to
assemble to the object in semiring category
-/
@[simp]
theorem forget₂_obj_SemiRingCat_of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    SemiRingCat.of (of M R) = SemiRingCat.of R :=
  rfl
-- It is said this is not used?

/--
Forgeting a morphism in the action category to semiring category
is defeq to
the coesion to the underlying semiring morphism in the semiring category
-/
@[simp]
theorem forget₂_map (R S : MulSemiringActionCat M) (f : R ⟶ S) :
    (forget₂ (MulSemiringActionCat M) SemiRingCat).map f = MulSemiringActionHom.toRingHom f :=
  rfl

/-- Typecheck a `MulSemiringActionHom` as a morphism in `MulSemiringActionCat M`. -/
def ofHom {R S : Type v} [Semiring R] [MulSemiringAction M R] [Semiring S]
    [MulSemiringAction M S] (f : MulSemiringActionHom M R S) : of M R ⟶ of M S :=
  f

-- why simp 1100
@[simp]
theorem ofHom_apply {R S : Type v} [Semiring R] [MulSemiringAction M R]
    [Semiring S] [MulSemiringAction M S] (f : MulSemiringActionHom M R S) (r : R) : ofHom M f r = f r :=
  rfl

-- TODO?: Inhabited and Unique

-- Porting note: the simpNF linter complains, but we really need this?!
@[simp, nolint simpNF]
theorem coe_of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    (of M R : Type v) = R :=
  rfl

@[simp]
theorem id_apply {R: MulSemiringActionCat.{v} M} (r : R) :
    (𝟙 R : R → R) r = r :=
  rfl

@[simp]
theorem coe_comp {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g : R → T) = g ∘ f :=
  rfl

@[simp]
theorem comp_def {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl

@[simp]
lemma forget_map {R S : MulSemiringActionCat.{v} M} (f : R ⟶ S) :
    (forget (MulSemiringActionCat M)).map f = (f : R → S) :=
  rfl

#check MulSemiringActionCat M
#check (Action SemiRingCat (MonCat.of M))

-- toRingHom is a monoid map
-- TODO: add these to MulSemiringActionHom
@[simp]
theorem
  this_for_map_one' (R : Type*) [Semiring R] [MulSemiringAction M R] :
    MulSemiringAction.toRingHom M R 1 = 1
  := by
    apply RingHom.ext
    simp only [MulSemiringAction.toRingHom_apply, one_smul, RingHom.coe_one, id_eq, forall_const]

@[simp]
theorem
  this_for_map_mul' (R : Type*) [Semiring R] [MulSemiringAction M R] :
    ∀ (x y : M),
      MulSemiringAction.toRingHom M (↑R) (x * y) =
        MulSemiringAction.toRingHom M (↑R) x * MulSemiringAction.toRingHom M (↑R) y
  := by
    intros x y
    apply RingHom.ext
    simp only [MulSemiringAction.toRingHom_apply, RingHom.coe_mul, Function.comp_apply]
    intro r
    exact mul_smul x y r

-- @[simp]
def toRepHom (R : Type*) [Semiring R] [MulSemiringAction M R]:
  M →* R →+* R where
    toFun := MulSemiringAction.toRingHom M R
    map_one' := this_for_map_one' M R
    map_mul' := this_for_map_mul' M R

-- @[simp]
-- def comp (R S: Type*) [Semiring R] [Semiring S] [MulSemiringAction M R] [MulSemiringAction M S] (f: MulSemiringActionHom M R S) :
--     ∀ m : M, ∀ r : R, f (m • r) = m • f r := by
--       intros m r
--       exact MulSemiringActionHom.map_smul f m r

-- cat comp is type comp

-- def toSemiringHom (R S : Type*) [Semiring R] [Semiring S]
--   [MulSemiringAction M R] [MulSemiringAction M S]
--     (f : MulSemiringActionHom M R S):
--       R →+* S where
--         toFun := f
--         map_one' := f.map_one
--         map_mul' := f.map_mul
--         map_zero' := f.map_zero
--         map_add' := f.map_add

-- instance (R S : MulSemiringActionCat M) :
--   Coe (R ⟶ S) (R →+* S) where
--     coe f := {
--       toFun := f.toFun
--       map_one' := f.map_one'
--       map_mul' := f.map_mul'
--       map_zero' := f.map_zero'
--       map_add' := f.map_add'
--     }

-- instance (R S : Type) [Semiring R] [Semiring S] :
--   Coe (R →+* S) (R ⟶ S) where
--     coe := sorry

-- This seems to be defeq??? not needed
-- instance (R S : MulSemiringActionCat.{v} M) :
--     Coe (R ⟶ S) (MulSemiringActionHom M R S) where
--       coe f := {
--         toFun := f.toFun
--         map_smul' := MulActionHom.map_smul' f.toMulActionHom
--         map_one' := f.map_one'
--         map_mul' := f.map_mul'
--         map_zero' := f.map_zero'
--         map_add' := f.map_add'
--       }

-- variable (R S : MulSemiringActionCat M) (f: R ⟶ S)
-- #check (f : MulSemiringActionHom M R S)
-- #check (f : R →+* S)
-- #check (f : R → S)

-- Does the same as SemiRingCat.coe_of?? not needed
-- @[simp]
theorem that (R : Type u) [Semiring R] (ρ : M →* ↑R →+* ↑R) :
  ({ V := SemiRingCat.of R, ρ := ρ } : Action SemiRingCat (MonCat.of M)).V = SemiRingCat.of R := by
    rfl

@[simp]
theorem bar (M : Type) [Monoid M] :
    @Bundled.α Monoid (MonCat.of M) = M := by
  rfl

@[simp]
theorem this (M : Type) [Monoid M] (X : MulSemiringActionCat M):
  ((MonCat.of M) →* (MonCat.of (End (SemiRingCat.of X)))) = (M →* (End (SemiRingCat.of X))) := by
    rfl

-- @[simp]
--   theorem tttt (M : Type) [Monoid M] (X Y : MulSemiringActionCat M) (m : (MonCat.of M)) (f : X ⟶ Y) (r : X):
--     (((toRepHom M X) m) ≫ SemiRingCat.ofHom f) r = ( (toRepHom M X) m ) ∘ f := sorry
    -- (((toRepHom M X) m) ≫ SemiRingCat.ofHom f) r = f ( (toRepHom M X m) r ) := by sorry

-- @[simp]
-- theorem foo (M R : Type) [Monoid M] [Semiring R]
--   (ρ : (MonCat.of M) →* (MonCat.of (End (SemiRingCat.of R))))
--     (f : R →+* R) (m : M) :
--       (ρ m) ≫ SemiRingCat.ofHom f =
  -- SemiRingCat.ofHom g ≫ SemiRingCat.ofHom f = SemiRingCat.ofHom (f.comp g) := by
  --   rfl


def functor : MulSemiringActionCat M ⥤ Action SemiRingCat (MonCat.of M) where
  obj R := {
    V := SemiRingCat.of R
    ρ := toRepHom M R
  }
  map f := {
    hom := SemiRingCat.ofHom f
    comm := by
      -- aesop
      -- apply RingHom.ext
      -- intros r
      /-
      case a
      M : Type u
      inst : Monoid M
      X Y : MulSemiringActionCat M
      f : X ⟶ Y
      g : ↑(MonCat.of M)
      r : ↑(SemiRingCat.of ↑X)
      ⊢ ↑(↑(toRepHom M ↑X) g ≫ SemiRingCat.ofHom ↑f) r = ↑(SemiRingCat.ofHom ↑f ≫ ↑(toRepHom M ↑Y) g) r
      -/


      intros m
      apply RingHom.ext
      intros r
      simp only [SemiRingCat.coe_of] at r ⊢

      /-
      case a
      M : Type u
      inst✝ : Monoid M
      X✝ Y✝ : MulSemiringActionCat M
      f : X✝ ⟶ Y✝
      m : ↑(MonCat.of M)
      r : ↑X✝
      ⊢ ↑(↑(toRepHom M ↑X✝) m ≫ SemiRingCat.ofHom ↑f) r = ↑(SemiRingCat.ofHom ↑f ≫ ↑(toRepHom M ↑Y✝) m) r
      -/

      rw [MonCat.coe_of] at m
      -- -- why `simp [bar] at m` not work?

      sorry
  }
