import Mathlib

open scoped ContDiff
open scoped Nat

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Establish `hc : ContDiffAt ℂ (i : ℕ) Complex.exp z` using `Complex.contDiff_exp.contDiffAt`. Rewrite using `[← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]`. Simplify using `only [Function.comp]`. Rewrite using `[ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]`. Establish `h` using `congrFun (iteratedDeriv_cexp_const_mul i 1) z`.

Simplify using `only [one_mul, one_pow] at h`. Rewrite using `[h, Complex.norm_exp]`.
-/
theorem norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

/- English proof (translation)
Establish `hd : ∀ s, DifferentiableAt ℝ h s` using `fun s => (hh.differentiable (by simp)).differentiableAt`. Establish `hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s`. Use function extensionality and compare the values at `s`. Conclude with `(L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv`. Rewrite using `[← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]`.

Establish `hfh : ContDiff ℝ ∞ (fderiv ℝ h)` using `hh.fderiv_right (by simp)`. Express the relevant statement in the definitionally equal form `‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _`. Rewrite using `[iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr ?_ + _`.

Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[iteratedFDeriv_const_of_ne hi.ne']`. Simplify using the standard rewrite rules.
-/
theorem norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by
  have hd : ∀ s, DifferentiableAt ℝ h s := fun s =>
    (hh.differentiable (by simp)).differentiableAt
  have hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s := by
    funext s
    exact (L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]
  have hfh : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp

/- English proof (translation)
Introduce `V E _ _ _ _ _ _ B h hh hre n R`. Use `set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF`. Establish `hFc : Continuous F`. Use `continuous_finset_sum _ (fun j _ => ?_)` and prove the remaining obligations. Conclude with `(hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm`.

Take `⟨K, hK⟩` from `(isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn`. Use `⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩` and prove the remaining obligations. Establish `htb : t ∈ Metric.closedBall (0 : E) R` using `by simpa using ht`. Establish `hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K|`. Introduce `j hj`.

Establish `h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t` using `Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))`. Establish `h2 : F t ≤ K` using `(le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)`. Conclude with `(h1.trans h2).trans (le_abs_self K)`. Use `set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD`. Establish `hy0` using `norm_nonneg y`.

Establish `hB0` using `norm_nonneg B`. Establish `hK0` using `abs_nonneg K`. Establish `hD1 : 1 ≤ D`. Rewrite using `[hD]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hDge : ‖B‖ * ‖y‖ + |K| ≤ D`. Rewrite using `[hD]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hphi : ContDiff ℝ ∞ (fun t => B y t + h t)` using `(B y).contDiff.add hh`. Establish `hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t)` using `rfl`.

Rewrite using `[hcomp]`. Establish `key` using `norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t) (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D) (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero]) (fun i hi1 hin => by`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring

end GlobalTheory
