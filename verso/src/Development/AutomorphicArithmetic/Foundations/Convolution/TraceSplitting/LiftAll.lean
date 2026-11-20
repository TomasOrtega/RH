import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.T.liftAll :
    UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll := by
  intro h F E _ _ _ _ _ _ _ _ σ hσ hp n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn π
    induction π using Quotient.inductionOn with
    | _ π =>
      rcases h F E σ hσ hp n hn (fun m h1 h2 => ih m h2 h1) π with ⟨ι, hι, m, Q, hm, hc, hw⟩ | ⟨P, hP, -⟩
      · exact ⟨ι, hι, m, Q, hm, Fintype.card_pos_iff.1 (by omega), hw⟩
      · refine ⟨Unit, inferInstance, fun _ => n, fun _ => GlobalTheory.CuspRep.CG.mk P, fun _ => hn, ⟨()⟩, ?_⟩
        rw [UpperTheory.ConvolutionTheory.R.sumSat_unit]
        exact hP.1
