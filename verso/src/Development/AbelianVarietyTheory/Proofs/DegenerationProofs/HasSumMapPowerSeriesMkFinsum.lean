import Mathlib
open Module

namespace GlobalTheory

/- English proof (translation)
Introduce `O K Z _ _ _ _ φ h1 hX deg hfin a`. Use `set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF`. Establish `key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) → ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖ ≤ ‖φ PowerSeries.X‖ ^ n`. Introduce `n s hs`. Establish `hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣ (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F`.

Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Rewrite using `[map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]`. Establish `: (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z`. Rewrite using `[← finsum_mem_coe_finset]`.

Use `finsum_congr fun z => ?_` and prove the remaining obligations. Use `finsum_congr_Prop ?_ (fun _ => rfl)` and prove the remaining obligations. Apply `propext` to reduce the goal to its premises. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq]`. Conclude with `⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩`.

Rewrite using `[this, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]`. Distinguish the cases in `h : deg z = m`. Simplify using `[h]`.

Simplify using `[h, Ne.symm h]`. Take `⟨g, hg⟩` from `hdvd`. Establish `h2` using `congrArg φ hg`. Simplify using `only [map_sub, map_sum, map_mul, map_pow] at h2`. Rewrite using `[h2, norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_right (by positivity) (h1 g)`. Rewrite using `[HasSum, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hX`. Establish `hfn : {z | deg z < n}.Finite`.

Use `((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]`. Conclude with `⟨deg z, hz, rfl⟩`. Simplify using `only [SummationFilter.unconditional_filter]`.

Use `filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs`. Rewrite using `[dist_eq_norm]`. Conclude with `(key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn`.
-/
theorem hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by
  intro O K Z _ _ _ _ φ h1 hX deg hfin a
  classical
  set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF
  have key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) →
      ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖
        ≤ ‖φ PowerSeries.X‖ ^ n := by
    intro n s hs
    have hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣
        (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]
      have : (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z := by
        rw [← finsum_mem_coe_finset]
        refine finsum_congr fun z => ?_
        refine finsum_congr_Prop ?_ (fun _ => rfl)
        apply propext
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : deg z = m
      · simp [h]
      · simp [h, Ne.symm h]
    obtain ⟨g, hg⟩ := hdvd
    have h2 := congrArg φ hg
    simp only [map_sub, map_sum, map_mul, map_pow] at h2
    rw [h2, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (h1 g)
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hX
  have hfn : {z | deg z < n}.Finite := by
    refine ((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    exact ⟨deg z, hz, rfl⟩
  simp only [SummationFilter.unconditional_filter]
  filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs
  rw [dist_eq_norm]
  exact (key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn

end GlobalTheory
