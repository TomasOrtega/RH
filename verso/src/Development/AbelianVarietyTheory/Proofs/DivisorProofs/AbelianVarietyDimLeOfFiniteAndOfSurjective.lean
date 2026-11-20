import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.DimLe

section

attribute [local instance low] specializationOrder

/- English proof (translation)
Establish `eX : topologicalKrullDim X = Order.krullDim X` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))`. Establish `eY : topologicalKrullDim Y = Order.krullDim Y` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))`. Rewrite using `[eX, eY]`. Use `Order.krullDim_le_of_strictMono (f : X → Y) fun a b hab => ?_` and prove the remaining obligations. Establish `h1 : f b ⤳ f a` using `Specializes.map hab.le f.continuous`.

Use `lt_of_le_of_ne h1 fun e => hab.ne ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y X f inferInstance (f a)).2 b a e.symm rfl hab.le).symm`.
-/
theorem topologicalKrullDim_le_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY]
  refine Order.krullDim_le_of_strictMono (f : X → Y) fun a b hab => ?_
  have h1 : f b ⤳ f a := Specializes.map hab.le f.continuous
  refine lt_of_le_of_ne h1 fun e => hab.ne ?_
  exact ((GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y X f inferInstance (f a)).2 b a
    e.symm rfl hab.le).symm

/- English proof (translation)
Establish `eX : topologicalKrullDim X = Order.krullDim X` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))`. Establish `eY : topologicalKrullDim Y = Order.krullDim Y` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))`. Rewrite using `[eX, eY, Order.krullDim_eq_iSup_height]`. Use `iSup_le fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hs y`.

Establish `h : Order.height (f x) ≤ Order.height x` using `ENat.forall_natCast_le_iff_le.mp fun n hn => GlobalTheory.GenFibreDim.le_height_of_specializingMap hc.specializingMap n x hn`. Conclude with `(WithBot.coe_le_coe.mpr h).trans (Order.height_le_krullDim x)`.
-/
theorem topologicalKrullDim_le_of_surjective_of_isClosedMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hs : Function.Surjective f) (hc : IsClosedMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hs y
  have h : Order.height (f x) ≤ Order.height x :=
    ENat.forall_natCast_le_iff_le.mp fun n hn =>
      GlobalTheory.GenFibreDim.le_height_of_specializingMap hc.specializingMap n x hn
  exact (WithBot.coe_le_coe.mpr h).trans (Order.height_le_krullDim x)

end

/- English proof (translation)
Introduce `K _ A B f`. Establish `hA` using `GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A`. Establish `hB` using `GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B`. Use `⟨fun hf => ?_, fun hf => ?_⟩` and prove the remaining obligations. Establish `h` using `topologicalKrullDim_le_of_isFinite f.hom.left`.

Rewrite `h` using `[hA, hB]`. Conclude with `h` after adjusting the coercions. Use `A.ab.proper` as an intermediate fact. Use `B.ab.proper` as an intermediate fact. Establish `hw : f.hom.left ≫ B.X.hom = A.X.hom` using `Over.w f.hom`.

Establish `: UniversallyClosed (f.hom.left ≫ B.X.hom)` using `by rw [hw]; infer_instance`. Establish `: UniversallyClosed f.hom.left` using `UniversallyClosed.of_comp_of_isSeparated f.hom.left B.X.hom`. Establish `h` using `topologicalKrullDim_le_of_surjective_of_isClosedMap f.hom.left hf.surj f.hom.left.isClosedMap`. Rewrite `h` using `[hA, hB]`. Conclude with `h` after adjusting the coercions.
-/
theorem dim_le : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  intro K _ A B f
  have hA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have hB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h := topologicalKrullDim_le_of_isFinite f.hom.left
    rw [hA, hB] at h
    exact_mod_cast h
  · have := A.ab.proper
    have := B.ab.proper
    have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
    have : UniversallyClosed (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed f.hom.left := UniversallyClosed.of_comp_of_isSeparated f.hom.left B.X.hom
    have h := topologicalKrullDim_le_of_surjective_of_isClosedMap f.hom.left
      hf.surj f.hom.left.isClosedMap
    rw [hA, hB] at h
    exact_mod_cast h

end GlobalTheory.AV.DimLe
