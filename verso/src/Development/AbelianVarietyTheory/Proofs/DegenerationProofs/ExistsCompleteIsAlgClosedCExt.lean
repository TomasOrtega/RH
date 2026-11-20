import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

/- English proof (translation)
Introduce `W _ _ _ K _ _ _`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `hmax : IsLocalRing.maximalIdeal W = Ideal.span {π}` using `hπ.maximalIdeal_eq`. Establish `hπm : π ∈ IsLocalRing.maximalIdeal W` using `hmax ▸ Ideal.mem_span_singleton_self π`. Take `⟨C, i1, i2, i3, i4, i5, h1, h2⟩` from `GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm (r := 1 / 2) (by norm_num) (by norm_num)`.

Establish `hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1` using `fun r => (h1 _).2 ⟨r, rfl⟩`. Set `g : K →ₐ[FractionRing W] C` to `IsAlgClosed.lift`. Use `⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[hmax, Ideal.mem_span_singleton]`. Take `⟨s, rfl⟩` from `hr`.

Rewrite using `[map_mul, map_mul, norm_mul, h2]`. Use `hle s` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := IsAlgClosed.lift
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
