import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

open Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

/- English proof (translation)
Introduce `P L hTT hL b hb u hu π`. Establish `hLaw : (MA.DQ P).Laws P.TT` using `Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le`. Establish `hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C`. Proceed by induction on `hb using Submonoid.closure_induction with`. Consider the case `mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx`.

Consider the case `one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩`. Consider the case `mul x y _ _ h1 h2`. Take `⟨C1, h1⟩` from `h1`. Take `⟨C2, h2⟩` from `h2`. Conclude with `⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩`.

Take `⟨C, hC0, Mx, hMb, hMe⟩` from `hPW`. Establish `hmeas` using `jd_evQ_meas P (MA.actA P b u π)`. Establish `hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT)` using `fun π' => (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')`. Establish `hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT)` using `memLp_finsetSum _ fun π' _ => (hL2u π').norm`. Establish `hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT)` using `hs.const_mul C`.

Use `(memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))` and prove the remaining obligations. Rewrite using `[hMe u q π]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)`.

Use `_ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm`. Use `_ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _`.
-/
theorem bounded_operators_square_integrable : BoundedOperatorsSquareIntegrable := by
  intro P L hTT hL b hb u hu π
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le
  have hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C := by
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx
    | one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩
    | mul x y _ _ h1 h2 =>
      obtain ⟨C1, h1⟩ := h1
      obtain ⟨C2, h2⟩ := h2
      exact ⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩
  obtain ⟨C, hC0, Mx, hMb, hMe⟩ := hPW
  have hmeas := jd_evQ_meas P (MA.actA P b u π)
  have hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT) := fun π' =>
    (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')
  have hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) :=
    memLp_finsetSum _ fun π' _ => (hL2u π').norm
  have hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) := hs.const_mul C
  refine (memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))
  rw [hMe u q π]
  calc ‖∑ π', Mx q π π' * MA.evQ P (u π') q‖ ≤ ∑ π', ‖Mx q π π' * MA.evQ P (u π') q‖ := norm_sum_le _ _
    _ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := Finset.sum_le_sum fun π' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)
    _ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _

end

end Formalism.FourierDecayAlt.P.CutMP
