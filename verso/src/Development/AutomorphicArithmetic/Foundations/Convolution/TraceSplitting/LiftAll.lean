import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep

/- English proof (translation)
Introduce `h F E _ _ _ _ _ _ _ _ σ hσ hp n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn π`. Proceed by induction on `π using Quotient.inductionOn with`.

Consider the case `_ π`. Break down `h F E σ hσ hp n hn (fun m h1 h2 => ih m h2 h1) π with ⟨ι, hι, m, Q, hm, hc, hw⟩ | ⟨P, hP, -⟩` into its components or cases. Conclude with `⟨ι, hι, m, Q, hm, Fintype.card_pos_iff.1 (by omega), hw⟩`. Use `⟨Unit, inferInstance, fun _ => n, fun _ => GlobalTheory.CuspRep.CG.mk P, fun _ => hn, ⟨()⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.ConvolutionTheory.R.sumSat_unit]`.

Conclude with `hP.1`.
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
