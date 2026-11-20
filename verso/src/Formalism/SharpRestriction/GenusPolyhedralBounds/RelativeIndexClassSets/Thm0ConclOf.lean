import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Introduce `large₂ X H S ka wL wF T nus β r hH1 hT hc hle hr hs hb hL`. Use `⟨r, hr, hs, hb, ?_⟩` and prove the remaining obligations. Introduce `la e he V' hV`. Establish `h0 : (0 : ℝ) ≤ (T : ℝ) * nus la` using `mul_nonneg (Nat.cast_nonneg _) (hH1.1 la)`. Establish `he0 : (0 : ℤ) ≤ e`.

Establish `: (0 : ℝ) ≤ (e : ℝ)` using `h0.trans he`. Conclude with `this` after adjusting the coercions. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le he0`. Establish `he' : (T : ℝ) * nus la ≤ (n : ℝ)` using `by simpa using he`. Take `⟨L, hOk, herr⟩` from `hL la n he'`.

Take `⟨h1, h2⟩` from `h large₂ X H S ka wL wF T nus la n hH1 hT hc hle he' L hOk V' hV`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h3 : (((n : ℤ) : ℝ)) = (n : ℝ)` using `by simp`. Rewrite using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thm0Concl_of (h : Thm0Local (D := D) (B := B) (P := P) (j := j)) :
    Thm0Concl (D := D) (B := B) (P := P) (j := j) := by
  intro large₂ X H S ka wL wF T nus β r hH1 hT hc hle hr hs hb hL
  refine ⟨r, hr, hs, hb, ?_⟩
  intro la e he V' hV
  have h0 : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hH1.1 la)
  have he0 : (0 : ℤ) ≤ e := by
    have : (0 : ℝ) ≤ (e : ℝ) := h0.trans he
    exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he0
  have he' : (T : ℝ) * nus la ≤ (n : ℝ) := by simpa using he
  obtain ⟨L, hOk, herr⟩ := hL la n he'
  obtain ⟨h1, h2⟩ := h large₂ X H S ka wL wF T nus la n hH1 hT hc hle he' L hOk V' hV
  refine ⟨h1, ?_⟩
  have h3 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
  rw [h3]
  linarith

end Formalism.MainNotions.Gaps.T0
