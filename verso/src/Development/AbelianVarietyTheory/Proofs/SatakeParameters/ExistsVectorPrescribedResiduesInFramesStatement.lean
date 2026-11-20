import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedResiduesInFrames
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CRTFrame.approx_frames_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsVectorPrescribedResiduesInFrames.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.exists_vector_prescribed_residues_in_frames : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  first | exact @GlobalTheory.CRTFrame.approx_frames_target | exact GlobalTheory.CRTFrame.approx_frames_target | (intros; apply GlobalTheory.CRTFrame.approx_frames_target <;> assumption)
