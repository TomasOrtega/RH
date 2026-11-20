import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `hD k r Wp Wq _ _ _ _ _ _ D A F hT hC`. Take `⟨hmeas, hbd⟩` from `hD k r Wp Wq D A 0 F hT hC`. Establish `hx : Continuous (fun p : SS k r => xiP D p)` using `by clear hmeas hbd hD hT hC`. Unfold `xiP psi ell`. Use `Continuous.mul ?_ (Continuous.star ?_)` and prove the remaining obligations.

Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))))) split_ifs` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Use `fun_prop`. Simplify using `only [Matrix.of_apply, Matrix.mulVec, dotProduct]`. Use `fun_prop`.

Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))))) split_ifs` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Use `fun_prop`. Simplify using `only [Matrix.of_apply, Matrix.mulVec, dotProduct]`. Use `fun_prop`.

Establish `h0 : (0 : ℕ) + 0 ≤ 0` using `le_rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨b, hb, hbb⟩` from `hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)`. Establish `hbg` using `hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)`.

Establish `hm` using `hmeas [] [] (by simp) (by simp) h0 g hg`. Use `Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_` and prove the remaining obligations. Use `filter_upwards [hbg] with p hp`. Combine the equalities or inequalities in the displayed calculation. Introduce `K hK hKO`.

Take `⟨b, hb, hbb⟩` from `hbd K hK hKO`. Conclude with `⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩`.
-/
theorem jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by
  intro hD k r Wp Wq _ _ _ _ _ _ D A F hT hC
  obtain ⟨hmeas, hbd⟩ := hD k r Wp Wq D A 0 F hT hC
  have hx : Continuous (fun p : SS k r => xiP D p) := by
    clear hmeas hbd hD hT hC
    unfold xiP psi ell
    refine Continuous.mul ?_ (Continuous.star ?_)
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
  have h0 : (0 : ℕ) + 0 ≤ 0 := le_rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hbb⟩ := hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)
    have hbg := hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)
    have hm := hmeas [] [] (by simp) (by simp) h0 g hg
    refine Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbg] with p hp
    calc ‖xiP D p • rho D p F g‖ = ‖xiP D p‖ * ‖rho D p F g‖ := norm_smul _ _
      _ ≤ 1 * ‖rho D p F g‖ := by gcongr; exact SmoothnessOnGoodSet.norm_xiP D p
      _ = ‖rho D p (dLR (List.map (AdL p) []) (List.map (AdR p) []) F) g‖ := by rw [one_mul]; rfl
      _ ≤ b p := hp
  · intro K hK hKO
    obtain ⟨b, hb, hbb⟩ := hbd K hK hKO
    exact ⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩

end Formalism.FourierDecayAlt.P.JFxDs1
