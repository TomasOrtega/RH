import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVect
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTameIwahoriTorusCharVectorOfParahoricDetCharVect.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsTame χ → IsParahoricVec χ π v → IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  first | exact @GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | exact GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | (intros; apply GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec <;> assumption)
