import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Introduce `D Ω _ _ κ _ d e hfr hFS`. Establish `hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ i j, Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ)) (ResSym.symMeasure d)` using `fun n r b hb => ResSym.integrable_gram d hb.1`. Establish `hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → (bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef` using `fun n r b hb => ResSym.posDef_gram d hb`. Take `⟨k₁, C₁, h₁⟩` from `ResChiSandwich.upper hfr hFS hint hpd (ResSym.sup_le_gram hR d)`. Take `⟨k₂, C₂, h₂⟩` from `ResChiSandwich.lower hfr hFS (ResSym.symMeasure_compl_pts d) hint hpd`.

Establish `hmono : Monotone (chiP D)` using `monotone_nat_of_le_succ fun n => by`. Use `chiP_succ_sub_nonneg D n` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hδ : (0 : ℝ) ≤ (projDeg d.x e : ℝ)` using `Nat.cast_nonneg _`. Use `⟨max k₁ k₂, max C₁ C₂, fun n hn => ?_⟩` and prove the remaining obligations.

Take `⟨b₀, hb₀⟩` from `exists_isSecBasis d.x n`. Establish `h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2` using `⟨⟨_, b₀⟩, hb₀⟩`. Rewrite using `[ResSym.resChi_eq d n h]`. Establish `hX : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1)` using `mul_nonneg (by positivity) (Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))`. Establish `hu` using `h₁ n (by omega) _ _ h.choose_spec`.

Establish `hl` using `h₂ n (by omega) _ _ h.choose_spec`. Prove the components needed by the constructor for the conclusion. Establish `hm : chiP D (n - max k₁ k₂) ≤ chiP D (n - k₂)` using `hmono (by omega)`. Establish `hm'` using `mul_le_mul_of_nonneg_left hm hδ`. Establish `hc : C₂ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1)`.

Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_right _ _) hX`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : chiP D (n + k₁) ≤ chiP D (n + max k₁ k₂)` using `hmono (by omega)`. Establish `hm'` using `mul_le_mul_of_nonneg_left hm hδ`.

Establish `hc : C₁ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1)`. Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) hX`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ResChiBounds.proof (hR : ResolutionSupBound.Statement) : ResChiBounds.Statement := by
  intro D Ω _ _ κ _ d e hfr hFS
  have hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
        (ResSym.symMeasure d) := fun n r b hb => ResSym.integrable_gram d hb.1
  have hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b →
      (bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef :=
    fun n r b hb => ResSym.posDef_gram d hb
  obtain ⟨k₁, C₁, h₁⟩ := ResChiSandwich.upper hfr hFS hint hpd (ResSym.sup_le_gram hR d)
  obtain ⟨k₂, C₂, h₂⟩ := ResChiSandwich.lower hfr hFS (ResSym.symMeasure_compl_pts d) hint hpd
  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hδ : (0 : ℝ) ≤ (projDeg d.x e : ℝ) := Nat.cast_nonneg _
  refine ⟨max k₁ k₂, max C₁ C₂, fun n hn => ?_⟩
  obtain ⟨b₀, hb₀⟩ := exists_isSecBasis d.x n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 := ⟨⟨_, b₀⟩, hb₀⟩
  rw [ResSym.resChi_eq d n h]
  have hX : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hu := h₁ n (by omega) _ _ h.choose_spec
  have hl := h₂ n (by omega) _ _ h.choose_spec
  constructor
  · have hm : chiP D (n - max k₁ k₂) ≤ chiP D (n - k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₂ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
    linarith
  · have hm : chiP D (n + k₁) ≤ chiP D (n + max k₁ k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₁ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
