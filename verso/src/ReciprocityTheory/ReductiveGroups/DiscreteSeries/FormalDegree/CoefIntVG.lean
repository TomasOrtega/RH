import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefOp

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Conclude with `(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional`.
-/
theorem coefIntVG_toE_continuous (n : ℕ) :
    Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

/- English proof (translation)
Take `⟨σ, hσ⟩` from `S7.exists_signVG ε`. Establish `hq1 : (1 : ℝ) ≤ S7.q0 ε` using `by exact_mod_cast hq`. Use `set c : ℝ := Real.sqrt (2 * S7.q0 ε) with hcdef`. Establish `hc1 : 1 ≤ c` using `Real.one_le_sqrt.mpr (by linarith)`. Establish `hc0 : 0 < c` using `by linarith`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hNc : ((2 * (n * Fintype.card (S7.SgIxV ε σ)) : ℕ) : ℝ) = 2 * ((n : ℝ) * S7.q0 ε)`. Rewrite using `[hσ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hh : 0 ≤ h`. Establish `: 0 ≤ 8 * c * (N + 2 * (n : ℝ) * S7.q0 ε)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set F : S7.UJ ε → ℝ := fun g => ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N with hFdef`. Establish `hfc : Continuous fun g : S7.UJ ε => Ψ (S7.toM g)` using `hcont.comp_continuous (S7.continuous_toM ε) (fun g => g.2)`.

Establish `hoc : Continuous fun g : S7.UJ ε => ‖Matrix.toEuclideanCLM (𝕜` using `ℂ) (S7.toM g)‖ := ((coefIntVG_toE_continuous n).comp (S7.continuous_toM ε)).norm`. Establish `hFc : Continuous F` using `hfc.norm.mul (hoc.rpow_const (fun _ => Or.inr hN))`. Use `set M : ℝ := Real.sqrt ((n : ℝ) * Real.exp 2 + 1) ^ N with hMdef`. Establish `hM1 : 1 ≤ M`. Use `Real.one_le_rpow ?_ hN` and prove the remaining obligations.

Use `Real.one_le_sqrt.mpr ?_` and prove the remaining obligations. Establish `: 0 ≤ (n : ℝ) * Real.exp 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF0 : ∀ g, 0 ≤ F g` using `fun g => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)`. Use `S7.integrable_of_decayVG ε σ ν F hFc.aestronglyMeasurable M (fun g hg => ?_) (h / (8 * c) - N) ?_ (fun g hg => ?_)` and prove the remaining obligations.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (hF0 g)]`. Establish `hop : ‖Matrix.toEuclideanCLM (𝕜` using `ℂ) (S7.toM g)‖ ≤ Real.sqrt ((n : ℝ) * Real.exp 2 + 1) := (coefOp_le_sqrt_hs _).trans (Real.sqrt_le_sqrt hg)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hNc, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨k, X, hX, hg'⟩` from `S7.polar_exists (ε := ε) (g := S7.toM g) g.2 set r : ℝ := Real.sqrt (S7.hs X) with hrdef`. Establish `hr0 : 0 ≤ r` using `Real.sqrt_nonneg _`. Establish `hr1 : S7.hs (S7.toM g) ≤ n * Real.exp (2 * r)`. Rewrite using `[hg', S7.hs_kmulVG]`. Conclude with `S7.hs_exp_leVG X`.

Use `⟨r, hr1, ?_⟩` and prove the remaining obligations. Establish `h1 : (n : ℝ) * Real.exp 2 < n * Real.exp (2 * r)` using `by linarith`. Establish `h2 : Real.exp 2 < Real.exp (2 * r)` using `lt_of_mul_lt_mul_left h1 hn0`. Establish `h3 : 1 < r` using `by have := Real.exp_lt_exp.mp h2; linarith`. Establish `h4 : r / c ≤ r ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hPsi : ‖Ψ (S7.toM g)‖ ≤ Real.exp (-((h / (8 * c)) * r))`. Rewrite using `[hg']`. Use `(hDec k X hX).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hhs : S7.hs X = r ^ 2` using `by rw [hrdef, Real.sq_sqrt (S7.hs_nonnegVG X)]`.

Establish `e : min (S7.hs X) (Real.sqrt (S7.hs X) / c) = r / c`. Rewrite using `[← hrdef, hhs]`. Conclude with `min_eq_right h4`. Rewrite using `[e]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hop : ‖Matrix.toEuclideanCLM (𝕜` using `ℂ) (S7.toM g)‖ ^ N ≤ Real.exp (N * r) := by`. Rewrite using `[hg']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (hF0 g)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ M * Real.exp (-((h / (8 * c) - N) * r)) := le_mul_of_one_le_left (Real.exp_pos _).le hM1`.
-/
theorem integrable_opPow_of_dec (Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hcont : ContinuousOn Ψ {g | inUJ ε g}) (hle : ∀ g, inUJ ε g → ‖Ψ g‖ ≤ 1)
    {h : ℝ} (hq : 1 ≤ S7.q0 ε)
    (hDec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    {N : ℝ} (hN : 0 ≤ N)
    (hthr : 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) * (N + 2 * (n : ℝ) * S7.q0 ε) < h)
    (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    Integrable (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) ν := by
  obtain ⟨σ, hσ⟩ := S7.exists_signVG ε
  have hq1 : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq
  set c : ℝ := Real.sqrt (2 * S7.q0 ε) with hcdef
  have hc1 : 1 ≤ c := Real.one_le_sqrt.mpr (by linarith)
  have hc0 : 0 < c := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNc : ((2 * (n * Fintype.card (S7.SgIxV ε σ)) : ℕ) : ℝ) = 2 * ((n : ℝ) * S7.q0 ε) := by
    rw [hσ]; push_cast; ring
  have hh : 0 ≤ h := by
    have : 0 ≤ 8 * c * (N + 2 * (n : ℝ) * S7.q0 ε) := by positivity
    linarith
  set F : S7.UJ ε → ℝ := fun g =>
    ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N with hFdef
  have hfc : Continuous fun g : S7.UJ ε => Ψ (S7.toM g) :=
    hcont.comp_continuous (S7.continuous_toM ε) (fun g => g.2)
  have hoc : Continuous fun g : S7.UJ ε => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ :=
    ((coefIntVG_toE_continuous n).comp (S7.continuous_toM ε)).norm
  have hFc : Continuous F := hfc.norm.mul (hoc.rpow_const (fun _ => Or.inr hN))
  set M : ℝ := Real.sqrt ((n : ℝ) * Real.exp 2 + 1) ^ N with hMdef
  have hM1 : 1 ≤ M := by
    refine Real.one_le_rpow ?_ hN
    refine Real.one_le_sqrt.mpr ?_
    have : 0 ≤ (n : ℝ) * Real.exp 2 := by positivity
    linarith
  have hF0 : ∀ g, 0 ≤ F g := fun g => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  refine S7.integrable_of_decayVG ε σ ν F hFc.aestronglyMeasurable M (fun g hg => ?_)
    (h / (8 * c) - N) ?_ (fun g hg => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (hF0 g)]
    have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ≤ Real.sqrt ((n : ℝ) * Real.exp 2 + 1) :=
      (coefOp_le_sqrt_hs _).trans (Real.sqrt_le_sqrt hg)
    calc ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N ≤ 1 * M :=
          mul_le_mul (hle _ g.2) (Real.rpow_le_rpow (norm_nonneg _) hop hN)
            (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one
      _ = M := one_mul M
  · rw [hNc, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
    linarith
  · obtain ⟨k, X, hX, hg'⟩ := S7.polar_exists (ε := ε) (g := S7.toM g) g.2
    set r : ℝ := Real.sqrt (S7.hs X) with hrdef
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr1 : S7.hs (S7.toM g) ≤ n * Real.exp (2 * r) := by
      rw [hg', S7.hs_kmulVG]; exact S7.hs_exp_leVG X
    refine ⟨r, hr1, ?_⟩
    have h1 : (n : ℝ) * Real.exp 2 < n * Real.exp (2 * r) := by linarith
    have h2 : Real.exp 2 < Real.exp (2 * r) := lt_of_mul_lt_mul_left h1 hn0
    have h3 : 1 < r := by have := Real.exp_lt_exp.mp h2; linarith
    have h4 : r / c ≤ r ^ 2 := by
      calc r / c ≤ r := div_le_self hr0 hc1
        _ ≤ r ^ 2 := by nlinarith
    have hPsi : ‖Ψ (S7.toM g)‖ ≤ Real.exp (-((h / (8 * c)) * r)) := by
      rw [hg']
      refine (hDec k X hX).trans (le_of_eq ?_)
      have hhs : S7.hs X = r ^ 2 := by rw [hrdef, Real.sq_sqrt (S7.hs_nonnegVG X)]
      have e : min (S7.hs X) (Real.sqrt (S7.hs X) / c) = r / c := by
        rw [← hrdef, hhs]; exact min_eq_right h4
      rw [e]
      congr 1
      ring
    have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N ≤ Real.exp (N * r) := by
      rw [hg']
      calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toMK k * NormedSpace.exp X)‖ ^ N
          ≤ Real.exp r ^ N := Real.rpow_le_rpow (norm_nonneg _) (coefOp_kexp k X) hN
        _ = Real.exp (N * r) := by rw [← Real.exp_mul]; ring_nf
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 g)]
    calc ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N
        ≤ Real.exp (-((h / (8 * c)) * r)) * Real.exp (N * r) :=
          mul_le_mul hPsi hop (Real.rpow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = Real.exp (-((h / (8 * c) - N) * r)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ M * Real.exp (-((h / (8 * c) - N) * r)) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hM1

end ReciprocityTheory.ChartRestriction.DS
