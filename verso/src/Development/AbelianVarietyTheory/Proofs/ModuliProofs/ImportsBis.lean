import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnitBallVal

/- English proof (translation)
Distinguish the cases in `ha : algebraMap O C a = 0`. Establish `hb : algebraMap O C b = 0`. Rewrite `h` using `[ha, norm_zero]`. Conclude with `norm_le_zero_iff.mp h`. Establish `hb0 : b = 0` using `hinj (by rw [hb, map_zero])`.

Rewrite using `[hb0]`. Conclude with `dvd_zero a`. Take `⟨y, hy⟩` from `hsurj (algebraMap O C b / algebraMap O C a) (by`. Rewrite using `[norm_div]`. Conclude with `(div_le_one (norm_pos_iff.mpr ha)).mpr h)`.

Use `⟨y, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hy]`. Clear the denominators using the available nonvanishing facts.
-/
theorem dvd_of_norm_le {C O : Type} [NormedField C] [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C))
    (hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x) {a b : O}
    (h : ‖algebraMap O C b‖ ≤ ‖algebraMap O C a‖) : a ∣ b := by
  by_cases ha : algebraMap O C a = 0
  · have hb : algebraMap O C b = 0 := by
      rw [ha, norm_zero] at h
      exact norm_le_zero_iff.mp h
    have hb0 : b = 0 := hinj (by rw [hb, map_zero])
    rw [hb0]
    exact dvd_zero a
  · obtain ⟨y, hy⟩ := hsurj (algebraMap O C b / algebraMap O C a) (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr h)
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy]
    field_simp

/- English proof (translation)
Introduce `C O _ _ _ _ hO`. Take `⟨hinj, hball⟩` from `hO`. Establish `hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x` using `fun x hx => (hball x).mpr hx`. Establish `hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1` using `fun y => (hball _).mp ⟨y, rfl⟩`. Establish `hdom : IsDomain O` using `hinj.isDomain (algebraMap O C)`.

Establish `hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y` using `fun y hy => isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))`. Use `⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩` and prove the remaining obligations. Break down `le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h` into its components or cases. Take `⟨c, hc⟩` from `dvd_of_norm_le hinj hsurj h`. Conclude with `⟨c, Or.inl hc.symm⟩`.

Take `⟨c, hc⟩` from `dvd_of_norm_le hinj hsurj h`. Conclude with `⟨c, Or.inr hc.symm⟩`. Take `⟨p, hpP, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Establish `hp' : algebraMap O C p ≠ 0` using `fun h0 => hp0 (hinj (by rw [h0, map_zero]))`. Establish `key : ∀ m : O, m ∉ P → IsUnit m`.

Introduce `m hm`. Apply `hunit` to reduce the goal to its premises. Use `le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt`. Take `⟨c, hc⟩` from `dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n) (by rw [map_pow, norm_pow]; exact hn.le)`.

Use `hP.mem_of_pow_mem n ?_` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `P.mul_mem_right c hpP`. Take `⟨M, hM, hPM⟩` from `Ideal.exists_le_maximal P hP.ne_top`. Establish `hMP : M ≤ P` using `fun m hm => by`.

Assume the negation of the conclusion as `hmP`. Conclude with `hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))`. Rewrite using `[le_antisymm hPM hMP]` and apply the resulting hypothesis. Use `(isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`.

Conclude with `IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))`. Introduce `z`. Distinguish the cases in `hz : ‖z‖ ≤ 1`. Take `⟨y, hy⟩` from `hsurj z hz`. Conclude with `⟨⟨y, 1⟩, by simp [hy]⟩`.

Rewrite `hz` using `[not_le]`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨y, hy⟩` from `hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)`. Establish `hy0 : y ∈ nonZeroDivisors O` using `mem_nonZeroDivisors_of_ne_zero (by`. Introduce and unpack `rfl`. Rewrite `hy` using `[map_zero]`. Conclude with `inv_ne_zero hz0 hy.symm)`.

Conclude with `⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩`. Introduce `x y hxy`. Conclude with `⟨1, by rw [hinj hxy]⟩`.
-/
theorem main : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing O] [Algebra O C], IsUnitBall O C → ∃ (_ : IsDomain O), ValuationRing O ∧ Ring.DimensionLEOne O ∧ IsFractionRing O C := by
  intro C O _ _ _ _ hO
  obtain ⟨hinj, hball⟩ := hO
  have hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x := fun x hx => (hball x).mpr hx
  have hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1 := fun y => (hball _).mp ⟨y, rfl⟩
  have hdom : IsDomain O := hinj.isDomain (algebraMap O C)

  have hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y := fun y hy =>
    isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))
  refine ⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩
  · rcases le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inr hc.symm⟩
  ·
    obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hp' : algebraMap O C p ≠ 0 := fun h0 => hp0 (hinj (by rw [h0, map_zero]))
    have key : ∀ m : O, m ∉ P → IsUnit m := by
      intro m hm
      apply hunit
      refine le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt
      obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n)
        (by rw [map_pow, norm_pow]; exact hn.le)
      refine hP.mem_of_pow_mem n ?_
      rw [hc]
      exact P.mul_mem_right c hpP
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hMP : M ≤ P := fun m hm => by
      by_contra hmP
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))
    rwa [le_antisymm hPM hMP]
  · refine (isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
    · intro z
      by_cases hz : ‖z‖ ≤ 1
      · obtain ⟨y, hy⟩ := hsurj z hz
        exact ⟨⟨y, 1⟩, by simp [hy]⟩
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz
          linarith
        obtain ⟨y, hy⟩ := hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)
        have hy0 : y ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (by
          rintro rfl
          rw [map_zero] at hy
          exact inv_ne_zero hz0 hy.symm)
        exact ⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩

end GlobalTheory.UnitBallVal
