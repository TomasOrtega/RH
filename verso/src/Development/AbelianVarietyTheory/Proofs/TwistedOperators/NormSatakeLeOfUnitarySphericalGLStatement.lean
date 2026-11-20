import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNormSatakeLeOfUnitarySphericalGL.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | exact GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | (intros; apply GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL <;> assumption)
