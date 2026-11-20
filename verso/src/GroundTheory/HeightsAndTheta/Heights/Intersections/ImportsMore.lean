import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G i Ψ hv hP' hP hΨ hi`. Take `⟨D, a, hDa, hDP, hcount⟩` from `hGood K ι K' ι' κ v P' n G i hv hP' hP hi`. Establish `hJ : IsMultiHomogIdeal (Ideal.span {D})` using `⟨{D}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hDa⟩, rfl⟩`. Establish `hJP : ¬ Ideal.span {D} ≤ imageZ v P'` using `fun hle => hDP (hle (Ideal.subset_span rfl))`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.mp (projB_null Ψ hP hΨ hJ hJP)] with y hy`.

Introduce and unpack `w ⟨z, hz, rfl, hΨz⟩`. Establish `hD : eval z (map (Int.castRingHom ℂ) D) ≠ 0`. Introduce `h0`. Use `hy ⟨z, hz, ⟨hz.1, fun f hf => ?_⟩, hΨz⟩` and prove the remaining obligations. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.mp hf`.

Rewrite using `[map_mul, map_mul, h0, mul_zero]`. Establish `hΨ0 : Ψ (segre z) 0 = 1`. Use `congrFun hΨz 0` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hcount z hz hD]`.

Use `congr 1`. Use extensionality with `O`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z', hz', rfl, hw⟩`. Use `⟨z', hz', rfl, ?_⟩` and prove the remaining obligations.

Establish `hμ : Ψ (segre fun p => z' (v p)) 0 ≠ 0`. Introduce `h0`. Rewrite `hw` using `[h0, inv_zero, zero_smul]`. Rewrite `hΨ0` using `[← hw, map_zero]`. Conclude with `zero_ne_one hΨ0`.

Use `sameOrbit_of_segre hz.1 (Ψ (segre fun p => z' (v p)) 0) hμ ?_` and prove the remaining obligations. Rewrite using `[← hw, smul_smul, mul_inv_cancel₀ hμ, one_smul]`. Introduce and unpack `⟨z', hz', rfl, hs⟩`. Use `⟨z', hz', rfl, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hcz⟩` from `hs`.

Establish `hμ : ∏ k, c k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Rewrite using `[hcz, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, hΨ0, mul_one, smul_smul, inv_mul_cancel₀ hμ, one_smul]`.
-/
theorem GenericPointsCount.proof (hGood : GenericPointsAvoidBadLocus.Statement) : GenericPointsCount.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n G i Ψ hv hP' hP hΨ hi
  obtain ⟨D, a, hDa, hDP, hcount⟩ := hGood K ι K' ι' κ v P' n G i hv hP' hP hi
  have hJ : IsMultiHomogIdeal (Ideal.span {D}) :=
    ⟨{D}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hDa⟩, rfl⟩
  have hJP : ¬ Ideal.span {D} ≤ imageZ v P' := fun hle => hDP (hle (Ideal.subset_span rfl))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (projB_null Ψ hP hΨ hJ hJP)] with y hy
  rintro w ⟨z, hz, rfl, hΨz⟩
  have hD : eval z (map (Int.castRingHom ℂ) D) ≠ 0 := by
    intro h0
    refine hy ⟨z, hz, ⟨hz.1, fun f hf => ?_⟩, hΨz⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero]
  have hΨ0 : Ψ (segre z) 0 = 1 := by
    have := congrFun hΨz 0
    simpa using this
  rw [← hcount z hz hD]
  congr 1
  ext O
  constructor
  · rintro ⟨z', hz', rfl, hw⟩
    refine ⟨z', hz', rfl, ?_⟩
    have hμ : Ψ (segre fun p => z' (v p)) 0 ≠ 0 := by
      intro h0
      rw [h0, inv_zero, zero_smul] at hw
      rw [← hw, map_zero] at hΨ0
      exact zero_ne_one hΨ0
    refine sameOrbit_of_segre hz.1 (Ψ (segre fun p => z' (v p)) 0) hμ ?_
    rw [← hw, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · rintro ⟨z', hz', rfl, hs⟩
    refine ⟨z', hz', rfl, ?_⟩
    obtain ⟨c, hc, hcz⟩ := hs
    have hμ : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    rw [hcz, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, hΨ0, mul_one, smul_smul, inv_mul_cancel₀ hμ,
      one_smul]

end GroundTheory.Heights₂.Heights.Inter
