import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)

/- English proof (translation)
Establish `he : 2 ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hla : 1 ≤ Real.log a`. Use `Real.log_le_log (Real.exp_pos 1) ha` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `h1 : b ≤ a * (1 + B)` using `by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]`. Establish `h2 : Real.log b ≤ Real.log a + Real.log (1 + B)`. Rewrite using `[← Real.log_mul ha0.ne' (by linarith)]`. Conclude with `Real.log_le_log hb h1`. Establish `h3 : Real.log (1 + B) ≤ B`.

Use `Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hla hB]`.
-/
theorem log_le_one_add_mul_log {a b B : ℝ} (ha : Real.exp 1 ≤ a) (hb : 0 < b) (hB : 0 ≤ B)
    (hab : b ≤ a + B) : Real.log b ≤ (1 + B) * Real.log a := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have h1 : b ≤ a * (1 + B) := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]
  have h2 : Real.log b ≤ Real.log a + Real.log (1 + B) := by
    rw [← Real.log_mul ha0.ne' (by linarith)]
    exact Real.log_le_log hb h1
  have h3 : Real.log (1 + B) ≤ B := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hla hB]

/- English proof (translation)
Introduce `X _ _ _ D A R hr Om C₁`. Take `⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩` from `hC D A R`. Establish `hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x` using `fun x hx => by`. Rewrite `hx` using `[← hYo]`. Establish `hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x)` using `mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)`.

Establish `: logNormSec L s x ≤ 0` using `Real.log_nonpos hpos.le (hs1 x)`. Simplify using `only [rSec]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0)` using `mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])`. Take `⟨CE, hCE⟩` from `hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁`.

Take `⟨CE', hCE'⟩` from `hS D (max B 0) CE`. Use `⟨CE', fun th u hT => ?_⟩` and prove the remaining obligations. Take `⟨hA, hpos, hmono⟩` from `hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT`. Establish `hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i)` using `fun i => by`. Establish `hTi` using `hT i`.

Use `⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i, by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hYo]`. Establish `hl` using `log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1]) (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])`. Establish `h0 : 0 ≤ Real.log (R.r x)` using `Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])`. Use `mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)` as an intermediate fact.

Use `mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0` as an intermediate fact. Use `hTi.le_u x hx` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Break down `hTi.smooth_or_pole with h | h` into its components or cases. Conclude with `Or.inl h`.

Use `right`. Rewrite using `[hYo]`. Conclude with `h`. Establish `h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE`. Establish `h1` using `hCE u hu`.

Rewrite `h1` using `[hYo]`. Introduce `R₀ hR₀`. Take `⟨hi, hle⟩` from `h1 R₀ hR₀`. Take `⟨hi', hle'⟩` from `hmono _ (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x) (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _) hi`. Conclude with `⟨hi', hle'.trans hle⟩`.

Conclude with `hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2`.
-/
theorem ListTailLog.proof (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := by
  intro X _ _ _ D A R hr Om C₁
  obtain ⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩ := hC D A R
  have hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x := fun x hx => by
    rw [← hYo] at hx
    have hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x) :=
      mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)
    have : logNormSec L s x ≤ 0 := Real.log_nonpos hpos.le (hs1 x)
    simp only [rSec]
    linarith
  have hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0) :=
    mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])
  obtain ⟨CE, hCE⟩ := hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁
  obtain ⟨CE', hCE'⟩ := hS D (max B 0) CE
  refine ⟨CE', fun th u hT => ?_⟩
  obtain ⟨hA, hpos, hmono⟩ := hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT
  have hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i) := fun i => by
    have hTi := hT i
    refine ⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i,
      by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩
    · rw [hYo] at hx
      have hl := log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1])
        (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])
      have h0 : 0 ≤ Real.log (R.r x) :=
        Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])
      have := mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0
      have := hTi.le_u x hx
      nlinarith
    · rcases hTi.smooth_or_pole with h | h
      · exact Or.inl h
      · right
        rw [hYo]
        exact h
  have h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE := by
    have h1 := hCE u hu
    rw [hYo] at h1
    intro R₀ hR₀
    obtain ⟨hi, hle⟩ := h1 R₀ hR₀
    obtain ⟨hi', hle'⟩ := hmono _
      (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg
        (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x)
      (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _) hi
    exact ⟨hi', hle'.trans hle⟩
  exact hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE
    (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2

end GroundTheory.Heights₂.Heights.AnalyticLimit
