import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `n e δ h Z f hd`. Take `⟨c, hc, g, hg, hf⟩` from `hd.chow`. Establish `hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0` using `mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)`. Establish `hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W)` using `hf ▸ hd.homog`. Take `⟨δW, hδW, hsum⟩` from `exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0`.

Establish `hW : ∀ W ∈ Z.support, IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧ ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) = -(δW W * (harmonic (n - 1) : ℝ)) / 2` using `fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)`. Establish `hint : ∀ W ∈ Z.support, IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h)` using `fun W hm => (hW W hm).1.const_mul _`. Unfold `cycleIntegral`. Use `⟨integrable_finsetSum _ hint, ?_⟩` and prove the remaining obligations. Rewrite using `[setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]`.

Establish `hterm : ∀ W ∈ Z.support, (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) = (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2)`. Introduce `W hm`. Rewrite using `[integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm]`.

Establish `hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ)`. Rewrite using `[← hsum]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CycleAverage.proof (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights
