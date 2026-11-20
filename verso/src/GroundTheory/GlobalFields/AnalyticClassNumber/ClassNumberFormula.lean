import Mathlib
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
set_option maxSynthPendingDepth 1

open NumberField InfinitePlace NumberField.Units Complex Topology Filter Set
open scoped Real

namespace GroundTheory.Global

noncomputable section

/- English proof (translation)
Establish `h' : Tendsto (fun s : ℂ ↦ 2 * (2 * (π : ℂ)) ^ (-s)) (𝓝[≠] 0) (𝓝 2)`. Rewrite using `[(by simp : 𝓝 (2 : ℂ) = 𝓝 (2 * (2 * (π : ℂ)) ^ (-(0 : ℂ))))]`. Use `Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds` and prove the remaining obligations. Conclude with `continuousAt_const.mul ((continuousAt_const_cpow (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))).comp (by fun_prop))`. Establish `h` using `h'.mul tendsto_self_mul_Gamma_nhds_zero`.

Rewrite `h` using `[mul_one]`. Use `h.congr fun z ↦ ?_` and prove the remaining obligations. Rewrite using `[Gammaℂ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Gammaℂ_residue_zero : Tendsto (fun s ↦ s * Gammaℂ s) (𝓝[≠] 0) (𝓝 2) := by
  have h' : Tendsto (fun s : ℂ ↦ 2 * (2 * (π : ℂ)) ^ (-s)) (𝓝[≠] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 (2 : ℂ) = 𝓝 (2 * (2 * (π : ℂ)) ^ (-(0 : ℂ))))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))).comp (by fun_prop))
  have h := h'.mul tendsto_self_mul_Gamma_nhds_zero
  rw [mul_one] at h
  refine h.congr fun z ↦ ?_
  rw [Gammaℂ]
  ring

variable (K : Type*) [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[← card_eq_nrRealPlaces_add_nrComplexPlaces]`. Conclude with `Fintype.card_pos`.
-/
theorem one_le_nrRealPlaces_add_nrComplexPlaces : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Fintype.card_pos

/- English proof (translation)
Establish `h` using `(Gammaℝ_residue_zero.pow (nrRealPlaces K)).mul (Gammaℂ_residue_zero.pow (nrComplexPlaces K))`. Rewrite `h` using `[← pow_add]`. Use `h.congr fun s ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_pow_mul_gamma_zero :
    Tendsto (fun s : ℂ ↦ s ^ (nrRealPlaces K + nrComplexPlaces K) *
      (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)) (𝓝[≠] 0)
      (𝓝 (2 ^ (nrRealPlaces K + nrComplexPlaces K))) := by
  have h := (Gammaℝ_residue_zero.pow (nrRealPlaces K)).mul
    (Gammaℂ_residue_zero.pow (nrComplexPlaces K))
  rw [← pow_add] at h
  refine h.congr fun s ↦ ?_
  ring

/- English proof (translation)
Establish `hd0 : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))).ne'`. Establish `hd : Tendsto (fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) (𝓝[≠] 0) (𝓝 1)`. Establish `hc : ContinuousAt (fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) 0` using `(continuousAt_const_cpow hd0).comp (by fun_prop)`. Establish `h1` using `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))`. Simplify using `using h1`.

Establish `hG` using `(tendsto_pow_mul_gamma_zero K).inv₀ (pow_ne_zero _ two_ne_zero)`. Establish `h` using `(hd.mul hG).mul (tendsto_mul_completedDedekindZeta_zero K)`. Establish `hlim : 1 * ((2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K))⁻¹ * -(((Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K : ℝ) : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹) = -((classNumber K * regulator K / torsionOrder K : ℝ) : ℂ)`. Rewrite using `[← normOneClassMeasure_univ_toReal_eq, normOneClassMeasure_univ_toReal_eq_classNumber]`. Establish `hπ : (π : ℂ) ≠ 0` using `ofReal_ne_zero.2 Real.pi_ne_zero`.

Establish `hw : ((torsionOrder K : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (Nat.cast_ne_zero.2 (torsionOrder_ne_zero K))`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hlim]`.

Take `⟨m, hm⟩ : ∃ m, nrRealPlaces K + nrComplexPlaces K = m + 1` from `⟨nrRealPlaces K + nrComplexPlaces K - 1, by`. Use `one_le_nrRealPlaces_add_nrComplexPlaces K` as an intermediate fact. Use the proof step `omega⟩`. Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Establish `hs0 : s ≠ 0` using `hs`. Rewrite using `[continuedDedekindZeta_of_ne_zero K hs0, normalizedDedekindZeta, hm, Nat.add_sub_cancel, pow_succ, mul_inv, mul_inv]`. Establish `hsm : s ^ m ≠ 0` using `pow_ne_zero _ hs0`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_continuedDedekindZeta_div_pow_zero :
    Tendsto (fun s ↦ continuedDedekindZeta K s / s ^ (nrRealPlaces K + nrComplexPlaces K - 1))
      (𝓝[≠] 0) (𝓝 (-((classNumber K * regulator K / torsionOrder K : ℝ) : ℂ))) := by
  have hd0 : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))).ne'
  have hd : Tendsto (fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) 0 :=
      (continuousAt_const_cpow hd0).comp (by fun_prop)
    have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
    simpa using h1
  have hG := (tendsto_pow_mul_gamma_zero K).inv₀ (pow_ne_zero _ two_ne_zero)
  have h := (hd.mul hG).mul (tendsto_mul_completedDedekindZeta_zero K)
  have hlim : 1 * ((2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K))⁻¹ *
      -(((Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K : ℝ) : ℂ) *
        ((π : ℂ) ^ nrComplexPlaces K)⁻¹) =
      -((classNumber K * regulator K / torsionOrder K : ℝ) : ℂ) := by
    rw [← normOneClassMeasure_univ_toReal_eq, normOneClassMeasure_univ_toReal_eq_classNumber]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hw : ((torsionOrder K : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (Nat.cast_ne_zero.2 (torsionOrder_ne_zero K))
    push_cast
    field_simp
    ring
  rw [hlim] at h
  obtain ⟨m, hm⟩ : ∃ m, nrRealPlaces K + nrComplexPlaces K = m + 1 :=
    ⟨nrRealPlaces K + nrComplexPlaces K - 1, by
      have := one_le_nrRealPlaces_add_nrComplexPlaces K; omega⟩
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  rw [continuedDedekindZeta_of_ne_zero K hs0, normalizedDedekindZeta, hm, Nat.add_sub_cancel, pow_succ,
    mul_inv, mul_inv]
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs0
  field_simp

/- English proof (translation)
Establish `hc : ContinuousAt (continuedDedekindZeta K) 0` using `(differentiableAt_continuedDedekindZeta K zero_ne_one).continuousAt`. Establish `hcw` using `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))`. Establish `h` using `tendsto_continuedDedekindZeta_div_pow_zero K`. Use `split_ifs with hr`. Rewrite `h` using `[hr, Nat.sub_self]`.

Simplify using `only [pow_zero, div_one] at h`. Conclude with `tendsto_nhds_unique hcw h`. Take `⟨k, hk⟩ : ∃ k, nrRealPlaces K + nrComplexPlaces K - 1 = k + 1` from `⟨nrRealPlaces K + nrComplexPlaces K - 2, by`. Use `one_le_nrRealPlaces_add_nrComplexPlaces K` as an intermediate fact. Use the proof step `omega⟩`.

Rewrite `h` using `[hk]`. Establish `hpow : Tendsto (fun s : ℂ ↦ s ^ (k + 1)) (𝓝[≠] 0) (𝓝 0)`. Use `((continuous_pow (k + 1)).tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))` as an intermediate fact. Simplify using `using this`. Establish `h0` using `h.mul hpow`.

Rewrite `h0` using `[mul_zero]`. Use `tendsto_nhds_unique hcw (h0.congr' ?_)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Establish `hs0 : s ^ (k + 1) ≠ 0` using `pow_ne_zero _ hs`. Clear the denominators using the available nonvanishing facts.
-/
theorem continuedDedekindZeta_zero :
    continuedDedekindZeta K 0 = if nrRealPlaces K + nrComplexPlaces K = 1 then
      -((classNumber K * regulator K / torsionOrder K : ℝ) : ℂ) else 0 := by
  have hc : ContinuousAt (continuedDedekindZeta K) 0 :=
    (differentiableAt_continuedDedekindZeta K zero_ne_one).continuousAt
  have hcw := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  have h := tendsto_continuedDedekindZeta_div_pow_zero K
  split_ifs with hr
  · rw [hr, Nat.sub_self] at h
    simp only [pow_zero, div_one] at h
    exact tendsto_nhds_unique hcw h
  · obtain ⟨k, hk⟩ : ∃ k, nrRealPlaces K + nrComplexPlaces K - 1 = k + 1 :=
      ⟨nrRealPlaces K + nrComplexPlaces K - 2, by
        have := one_le_nrRealPlaces_add_nrComplexPlaces K; omega⟩
    rw [hk] at h
    have hpow : Tendsto (fun s : ℂ ↦ s ^ (k + 1)) (𝓝[≠] 0) (𝓝 0) := by
      have := ((continuous_pow (k + 1)).tendsto (0 : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
      simpa using this
    have h0 := h.mul hpow
    rw [mul_zero] at h0
    refine tendsto_nhds_unique hcw (h0.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ^ (k + 1) ≠ 0 := pow_ne_zero _ hs
    field_simp

end

end GroundTheory.Global
