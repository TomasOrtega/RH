import Mathlib

noncomputable section

open Function

namespace PositivityTheory.Rg.Sw.SP

/- English proof (translation)
Establish `hdiff : ∀ k : ℕ, Differentiable ℂ ((swap dslope (0 : ℂ))^[k] f)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hf`. Consider the case `succ k ih`.

Rewrite using `[Function.iterate_succ_apply']`. Use `(Complex.differentiableOn_dslope (f := (swap dslope (0 : ℂ))^[k] f) (s := Set.univ) (c := 0) Filter.univ_mem).2 ih.differentiableOn` as an intermediate fact. Simplify `this` using `[swap, differentiableOn_univ]`. Take `⟨p, hp⟩` from `hf.analyticAt 0`. Take `⟨R, hR⟩` from `hp`.

Establish `hcoeff : ∀ k < r, p.coeff k = 0`. Introduce `k hk`. Establish `h1` using `hR.factorial_smul (y := (1 : ℂ)) k`. Establish `h2 : iteratedDeriv k f 0 = iteratedFDeriv ℂ k f 0 (fun _ => 1)`. Rewrite using `[iteratedDeriv_eq_iteratedFDeriv]`.

Rewrite `h1` using `[← h2, h k hk]`. Establish `h3 : p.coeff k = p k (fun _ => 1)` using `rfl`. Rewrite using `[h3]`. Rewrite `h1` using `[nsmul_eq_mul]`. Break down `mul_eq_zero.1 h1 with h4 | h4` into its components or cases.

Conclude with `absurd h4 (by exact_mod_cast Nat.factorial_ne_zero k)`. Conclude with `h4`. Establish `hzero : ∀ k < r, (swap dslope (0 : ℂ))^[k] f 0 = 0`. Introduce `k hk`. Use `(hR.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1` as an intermediate fact.

Rewrite using `[← this, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]`. Conclude with `hcoeff k hk`. Use `⟨(swap dslope (0 : ℂ))^[r] f, hdiff r, fun z => ?_⟩` and prove the remaining obligations. Use `pow_sub_smul_iterate_dslope_of_zero r hzero z` as an intermediate fact. Simplify `this.symm` using `[smul_eq_mul]`.
-/
theorem entire_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℕ)
    (h : ∀ j < r, iteratedDeriv j f 0 = 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ r * g z := by
  have hdiff : ∀ k : ℕ, Differentiable ℂ ((swap dslope (0 : ℂ))^[k] f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (Complex.differentiableOn_dslope (f := (swap dslope (0 : ℂ))^[k] f) (s := Set.univ) (c := 0)
        Filter.univ_mem).2 ih.differentiableOn
      simpa [swap, differentiableOn_univ] using this
  obtain ⟨p, hp⟩ := hf.analyticAt 0
  obtain ⟨R, hR⟩ := hp
  have hcoeff : ∀ k < r, p.coeff k = 0 := by
    intro k hk
    have h1 := hR.factorial_smul (y := (1 : ℂ)) k
    have h2 : iteratedDeriv k f 0 = iteratedFDeriv ℂ k f 0 (fun _ => 1) := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [← h2, h k hk] at h1
    have h3 : p.coeff k = p k (fun _ => 1) := rfl
    rw [h3]
    rw [nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h4 | h4
    · exact absurd h4 (by exact_mod_cast Nat.factorial_ne_zero k)
    · exact h4
  have hzero : ∀ k < r, (swap dslope (0 : ℂ))^[k] f 0 = 0 := by
    intro k hk
    have := (hR.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
    rw [← this, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
    exact hcoeff k hk
  refine ⟨(swap dslope (0 : ℂ))^[r] f, hdiff r, fun z => ?_⟩
  have := pow_sub_smul_iterate_dslope_of_zero r hzero z
  simpa [smul_eq_mul] using this.symm

end PositivityTheory.Rg.Sw.SP
