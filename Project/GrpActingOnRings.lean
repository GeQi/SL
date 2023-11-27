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
lemma ext {R S : MulSemiringActionCat.{v} M} {f₁ f₂ : R ⟶ S} (h : ∀ (r : R), f₁ r = f₂ r) :
    f₁ = f₂ :=
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
    [Semiring S] [MulSemiringAction M S] (f : MulSemiringActionHom M R S) (r : R) :
      ofHom M f r = f r :=
  rfl

-- TODO?: Inhabited and Unique

-- Porting note: the simpNF linter complains, but we really need this?!
@[simp, nolint simpNF]
theorem coe_of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    (of M R : Type v) = R :=
  rfl

-- or id_apply??
@[simp]
theorem coe_id {R: MulSemiringActionCat.{v} M}:
    (𝟙 R : R → R) = id :=
  rfl

@[simp]
theorem coe_comp {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g ∘ f :=
  rfl

@[simp]
theorem comp_def {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl

@[simp]
lemma forget_map {R S : MulSemiringActionCat.{v} M} (f : R ⟶ S) :
    (forget (MulSemiringActionCat M)).map f = (f : R → S) :=
  rfl

-- toRingHom is a monoid map
-- TODO: add these to MulSemiringActionHom
@[simp]
theorem
  this_for_map_one' (R : Type v) [Semiring R] [MulSemiringAction M R] :
    MulSemiringAction.toRingHom M R 1 = 1
  := by
    apply RingHom.ext
    simp only [MulSemiringAction.toRingHom_apply, one_smul, RingHom.coe_one, id_eq, forall_const]

@[simp]
theorem
  this_for_map_mul' (R : Type v) [Semiring R] [MulSemiringAction M R] :
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
def ρ (R : Type v) [Semiring R] [MulSemiringAction M R]:
  M →* R →+* R where
    toFun := MulSemiringAction.toRingHom M R
    map_one' := this_for_map_one' M R
    map_mul' := this_for_map_mul' M R

def F : MulSemiringActionCat M ⥤ Action SemiRingCat (MonCat.of M) where
  obj R := {
    V := SemiRingCat.of R
    ρ := ρ M R
  }
  map f := {
    hom := SemiRingCat.ofHom f
    comm := by
      intros m
      apply RingHom.ext
      intros r
      simp only [SemiRingCat.coe_of] at r ⊢
      change f (m • r) = m • f r
      exact map_smul f m r
  }

instance : CategoryTheory.Full (F M) where
  preimage {R S} := fun
    | .mk hom comm => {
      toFun := hom
      map_smul' := by
        intros m r
        change (SemiRingCat.ofHom (ρ M R m) ≫ hom) r
          = (hom ≫ (SemiRingCat.ofHom (ρ M S m))) r
        have h := comm m
        change SemiRingCat.ofHom (ρ M R m) ≫ hom
          = hom ≫ (SemiRingCat.ofHom (ρ M S m)) at h
        have t:
            (fun r => (SemiRingCat.ofHom (ρ M R m) ≫ hom) r)
              = (fun r => (hom ≫ (SemiRingCat.ofHom (ρ M S m))) r) :=
          FunLike.ext'_iff.mp (comm m)
        apply congrFun t r
      map_zero' := hom.map_zero'
      map_add' := hom.map_add'
      map_one' := hom.map_one'
      map_mul' := hom.map_mul'
    }

instance : CategoryTheory.Faithful (F M) where
  map_injective {_ _ a₁ a₂} h := by
    ext r
    calc
      a₁ r = ((F M).map a₁).hom r := rfl
      _ = ((F M).map a₂).hom r := congrFun (congrArg FunLike.coe (congrArg Action.Hom.hom h)) r
      _ = a₂ r := rfl

-- addd to other as well
def assemble (R: Type v) [Semiring R] (ρ : M →* R →+* R) : MulSemiringAction M R where
  smul m := ρ m
  one_smul r := by
    change ρ 1 r = r
    simp only [map_one, RingHom.coe_one, id_eq, forall_const]
  mul_smul g h r := by
    change ρ (g * h) r = (ρ g * ρ h) r
    simp only [map_mul, RingHom.coe_mul, Function.comp_apply, forall_const]
  smul_zero g := by
    change ρ g 0 = 0
    simp only [map_zero]
  smul_add g r s := by
    change ρ g (r + s) = ρ g r + ρ g s
    simp only [map_add]
  smul_one g := by
    change ρ g 1 = 1
    simp only [map_one]
  smul_mul g r s := by
    change ρ g (r * s) = ρ g r * ρ g s
    simp only [map_mul]

instance : CategoryTheory.EssSurj (F M) where
  mem_essImage
    | .mk V ρ => Functor.obj_mem_essImage (F M) (@of _ _ _ _ (assemble M V ρ))

theorem this : IsEquivalence (F M) := Equivalence.ofFullyFaithfullyEssSurj (F M)
