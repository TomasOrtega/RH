import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

/- English proof (translation)
Establish `h' : Filter.Tendsto (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal)` using `h`. Establish `hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal` using `ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0` using `by filter_upwards [self_mem_nhdsWithin] with r hr`.

Conclude with `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg) (pow_nonneg (le_of_lt hr) _)`. Use `le_of_tendsto h' hle` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

/- English proof (translation)
Establish `hc` using `pos_of_isGauge' h`. Establish `h' : Filter.Tendsto (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal)` using `h`. Establish `hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal` using `ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne`. Establish `hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Use `⟨hc, ?_⟩` and prove the remaining obligations.

Unfold `IsGaugeSub`. Use `⟨by simp, fun s _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_smul, map_mul_left_eq_self]`. Rewrite using `[← ENNReal.ofReal_toReal hfin]`. Use `(ENNReal.tendsto_ofReal h').congr' ?_` and prove the remaining obligations.

Use `filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0`. Establish `hr0' : (0 : ℝ) < r` using `hr0`. Establish `hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤`. Introduce `htop`. Rewrite `hr` using `[htop]`.

Simplify using `at hr`. Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _), ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]`.
-/
theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

/- English proof (translation)
Introduce `n ε`. Use `⟨fun c hc => isGaugeSub_univ hc, ?_⟩` and prove the remaining obligations. Take `⟨E, hE, horth, hexp⟩` from `GlobalTheory.LieONB.exists_orthonormal_basis n ε`. Use `⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, hX⟩`. Rewrite using `[hexp X hX]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i`. Use extensionality with `a b`.

Simplify using `[Complex.real_smul]`. Rewrite using `[hs]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `hX`. Use `⟨Submodule.mem_top, ?_⟩` and prove the remaining obligations.

Establish `hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1`. Conclude with `GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)`.

Use extensionality with `g`. Simplify using the standard rewrite rules.
-/
theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
