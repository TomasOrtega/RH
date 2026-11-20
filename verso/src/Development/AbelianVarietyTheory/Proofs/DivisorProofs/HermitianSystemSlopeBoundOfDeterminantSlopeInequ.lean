import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShortNum

/- English proof (translation)
Introduce `T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC`. Take `⟨hz0, hz1, hineq⟩` from `hC`. Unfold `Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG`. Use `set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz`. Use `⟨hz0, hz1, ?_⟩` and prove the remaining obligations.

Use `set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ`. Establish `hD1 : (1 : ℝ) ≤ D` using `by exact_mod_cast hD`. Establish `hT2 : (2 : ℝ) ≤ T`. Establish `: 2 ≤ T` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hTpos : (0 : ℝ) < T` using `by linarith`. Establish `hlogT : 0 ≤ Real.log T` using `Real.log_nonneg (by linarith)`. Establish `hlogn : 0 ≤ Real.log n` using `Real.log_nonneg hn`. Establish `hlogΛ : 0 ≤ Real.log Λ` using `Real.log_nonneg hΛ`. Establish `hlogβ : 0 ≤ Real.log β` using `Real.log_nonneg hβ`.

Establish `hβpos : 0 < β` using `by linarith`. Establish `h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T`. Rewrite using `[Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]`. Establish `h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2`. Rewrite using `[Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβpos.le]`.

Establish `hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ` using `by have := abs_nonneg h; linarith`. Establish `hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)`. Establish `a1 : n ≤ n * (D : ℝ)` using `by nlinarith`. Establish `a2 : n ≤ n * (D : ℝ) * 1 * δ` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ))`. Rewrite using `[← Real.log_mul (by norm_num) (by linarith)]`. Conclude with `Real.log_le_log (by linarith) hprod`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2`.

Unfold `HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]`. Establish `hc : HSShort.cst n Λ ≤ ρ` using `by rw [hcst, hρ]; linarith`. Establish `hc0 : 0 ≤ HSShort.cst n Λ` using `by rw [hcst]; positivity`. Rewrite using `[h1, h2]`. Use `clear h1 h2 hprod hlog2n hcst hX`.

Generalize the expression as in `HSShort.cst n Λ = c at *`. Use `clear_value ρ z`. Generalize the expression as in `(T : ℝ) = t at *`. Generalize the expression as in `(D : ℝ) = e at *`. Generalize the expression as in `Real.log t = lt at *`.

Generalize the expression as in `Real.log n = ln at *`. Generalize the expression as in `Real.log β = lb at *`. Establish `hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt) - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb`. Establish `e1 : t * h - t * ((ln + 1) / 2) ≤ t * h'`. Use `mul_le_mul_of_nonneg_left hh hTpos.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt)`. Establish `: e * (e + 1) ≤ 2 * e ^ 2` using `by nlinarith`. Establish `hD2 : 0 ≤ e ^ 2` using `by positivity`. Combine the linear relations using `[mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2, mul_nonneg hD2 hc0]`.

Establish `e3 : t / 2 * lb ≤ (t + e + 1) * lb` using `mul_le_mul_of_nonneg_right (by linarith) hlogβ`. Establish `e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)`. Establish `hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2`. Combine the linear relations using `[mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]`. Establish `hT' : t ≤ t + e ^ 2` using `by linarith [sq_nonneg e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `e5 : 0 ≤ 3 * (e + 1) * |h|` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT`. Establish `: t * c ≤ t * (Real.log 2 + ρ)` using `mul_le_mul_of_nonneg_left (by linarith) hTpos.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1' : 0 ≤ 1 - z` using `by linarith`. Establish `m1` using `mul_le_mul_of_nonneg_left hA hz1'`. Establish `m2` using `mul_le_mul_of_nonneg_left hB hz0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem claimS_to_hsClaimS : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ →
    h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  intro T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC
  obtain ⟨hz0, hz1, hineq⟩ := hC
  unfold Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG
  set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz
  refine ⟨hz0, hz1, ?_⟩
  set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hβpos : 0 < β := by linarith
  have h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]
  have h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt hβpos.le]
  have hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ := by have := abs_nonneg h; linarith
  have hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ) := by
    have a1 : n ≤ n * (D : ℝ) := by nlinarith
    have a2 : n ≤ n * (D : ℝ) * 1 * δ := by nlinarith
    nlinarith
  have hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hprod
  have hl2 := Real.log_two_gt_d9
  have hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2 := by
    unfold HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]
  have hc : HSShort.cst n Λ ≤ ρ := by rw [hcst, hρ]; linarith
  have hc0 : 0 ≤ HSShort.cst n Λ := by rw [hcst]; positivity
  rw [h1, h2]
  clear h1 h2 hprod hlog2n hcst hX
  generalize HSShort.cst n Λ = c at *
  clear_value ρ z
  generalize (T : ℝ) = t at *
  generalize (D : ℝ) = e at *
  generalize Real.log t = lt at *
  generalize Real.log n = ln at *
  generalize Real.log β = lb at *
  have hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt)
        - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)
      ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb := by
    have e1 : t * h - t * ((ln + 1) / 2) ≤ t * h' := by
      have := mul_le_mul_of_nonneg_left hh hTpos.le
      linarith
    have e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt) := by
      have : e * (e + 1) ≤ 2 * e ^ 2 := by nlinarith
      have hD2 : 0 ≤ e ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2,
        mul_nonneg hD2 hc0]
    have e3 : t / 2 * lb ≤ (t + e + 1) * lb := mul_le_mul_of_nonneg_right (by linarith) hlogβ
    have e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) := by
      have hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]
      have hT' : t ≤ t + e ^ 2 := by linarith [sq_nonneg e]
      calc t * ((ln + 1) / 2) ≤ t * ((e + 1) * (ln + 1) / 2 + 1 + 2) :=
            mul_le_mul_of_nonneg_left hg hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT' (by positivity)
    have e5 : 0 ≤ 3 * (e + 1) * |h| := by positivity
    linarith
  have hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT
      ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT := by
    have : t * c ≤ t * (Real.log 2 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hTpos.le
    linarith
  have hz1' : 0 ≤ 1 - z := by linarith
  have m1 := mul_le_mul_of_nonneg_left hA hz1'
  have m2 := mul_le_mul_of_nonneg_left hB hz0
  linarith

end GlobalTheory.HSShortNum
