import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatakeStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

open GlobalTheory.CuspRep

namespace PositivityTheory.jumpWindows

/- English proof (translation)
Introduce `h E _ _ _ a π π' e`. Use `congrArg CuspSub.V (h E a π π' ?_)` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.T.cuspidal_GL_local_components_eventually_satake CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw`. Take `⟨B, hB⟩` from `hw`. Conclude with `⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩`.
-/
theorem mean_convergence_of : Smo → GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  refine congrArg CuspSub.V (h E a π π' ?_)
  filter_upwards [GlobalTheory.T.cuspidal_GL_local_components_eventually_satake CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩

end PositivityTheory.jumpWindows
