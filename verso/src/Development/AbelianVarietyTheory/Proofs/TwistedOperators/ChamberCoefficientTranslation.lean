import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open MeasureTheory GlobalTheory.Chamber Filter Topology

noncomputable section

namespace GlobalTheory.Chamber

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sumM_expFam_shift {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X Y : Finset (SV k) → A0 k) (h : A0 k)
    (hY : ∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) (l : A0 k) :
    sumM 𝔞 Q (expFam Y) l = eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l := by
  unfold sumM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' := (mem_parP.1 hP).2.1
  have e : pr P h = 𝔞.starProjection h := by subst hP'; rfl
  simp only [expFam, hY P hP, e, eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cM_expFam_shift_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) →
      cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  intro hFS k 𝔞 hL Q hQ X Y hX h hY
  have hc := (hFS k 𝔞 hL (expFam X) hX.isGMFam Q hQ).1
  have t1 : Tendsto (sumM 𝔞 Q (expFam X)) (𝓝[generic k] 0) (𝓝 (cM 𝔞 Q (expFam X) 0)) :=
    ((hc.1.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun l hl => hc.2 hl)
  have hg : Continuous fun l : A0 k => eL l (𝔞.starProjection h) := by
    unfold eL; fun_prop
  have t2 : Tendsto (fun l : A0 k => eL l (𝔞.starProjection h)) (𝓝[generic k] 0) (𝓝 1) := by
    have := (hg.tendsto 0).mono_left (nhdsWithin_le_nhds (s := generic k))
    simpa [eL] using this
  have t3 := t2.mul t1
  rw [one_mul] at t3
  unfold cM
  refine extendFrom_eq (dense_generic 0) ?_
  have e : sumM 𝔞 Q (expFam Y) = fun l => eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l :=
    funext (sumM_expFam_shift 𝔞 Q X Y h hY)
  rw [e]
  exact t3

end GlobalTheory.Chamber
