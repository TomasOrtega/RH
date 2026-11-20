import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.PrimeSquareSum

/- English proof (translation)
Establish `hs` using `hasSum_zeta_two`. Establish `h1 : (1 : ℕ) ∉ t` using `fun h => by`. Use `ht 1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ n ∈ insert 1 t, ((n : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6`.

Rewrite using `[← hs.tsum_eq]`. Establish `e : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹`. Use function extensionality and compare the values at `n`. Rewrite using `[one_div]`. Rewrite using `[e]`.

Conclude with `Summable.sum_le_tsum _ (fun _ _ => by positivity) (e ▸ hs.summable)`. Rewrite `hsum` using `[Finset.sum_insert h1]`. Evaluate the numerical expressions using `at hsum`. Establish `hpi : Real.pi ^ 2 / 6 ≤ 2`. Use `Real.pi_lt_d2` as an intermediate fact.

Use polynomial arithmetic with `[Real.pi_pos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_inv_sq_le_one (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  have hs := hasSum_zeta_two
  have h1 : (1 : ℕ) ∉ t := fun h => by
    have := ht 1 h
    omega
  have hsum : ∑ n ∈ insert 1 t, ((n : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← hs.tsum_eq]
    have e : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
      funext n
      rw [one_div]
    rw [e]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (e ▸ hs.summable)
  rw [Finset.sum_insert h1] at hsum
  norm_num at hsum
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  linarith

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.exists_colouring_maximal_ideals K`. Establish `hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧ p ≤ Ideal.absNorm w.asIdeal`. Introduce `w`. Use `haveI := w.isMaximal`. Take `⟨q, n, hn, hqP, hq, H⟩` from `Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal`.

Conclude with `⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩`. Use `choose p hp hpm hple using hp`. Rewrite using `[← Finset.sum_fiberwise s (fun w => c w.asIdeal)]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Establish `hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i)`. Introduce `v hv w hw h`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw`. Conclude with `HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v) (h ▸ hpm w) (hv.2.trans hw.2.symm))`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations. Establish `h0 : (0 : ℝ) < p w` using `by exact_mod_cast (hp w).pos`. Establish `h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ)` using `by exact_mod_cast hple w`. Use `gcongr`. Use `_ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ := (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm`.

Use `_ ≤ 1 := by`. Use `sum_inv_sq_le_one _ fun n hn => ?_` and prove the remaining obligations. Take `⟨w, -, rfl⟩` from `Finset.mem_image.1 hn`. Conclude with `(hp w).two_le`. Use `_ = _ := by simp`.
-/
theorem sum_absNorm_inv_sq_le (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.exists_colouring_maximal_ideals K
  have hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧
      p ≤ Ideal.absNorm w.asIdeal := by
    intro w
    haveI := w.isMaximal
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    exact ⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩
  choose p hp hpm hple using hp
  rw [← Finset.sum_fiberwise s (fun w => c w.asIdeal)]
  calc _ ≤ ∑ _i : Fin (Module.finrank ℚ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i) := by
          intro v hv w hw h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          exact HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v)
            (h ▸ hpm w) (hv.2.trans hw.2.symm))
        calc _ ≤ ∑ w ∈ s.filter (fun w => c w.asIdeal = i), ((p w : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun w _ => ?_
              have h0 : (0 : ℝ) < p w := by exact_mod_cast (hp w).pos
              have h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast hple w
              gcongr
          _ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
          _ ≤ 1 := by
              refine sum_inv_sq_le_one _ fun n hn => ?_
              obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
              exact (hp w).two_le
    _ = _ := by simp

/- English proof (translation)
Introduce `K _ _`. Establish `hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹` using `fun w => by positivity`. Conclude with `⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K), tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩`.
-/
theorem summable_absNorm_inv_sq : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  intro K _ _
  have hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun w => by positivity
  exact ⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K),
    tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩

end GlobalTheory.PrimeSquareSum
