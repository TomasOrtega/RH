import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSatakeParameterOfSpherical.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.satake_parameter_of_spherical : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), GlobalTheory.LGrp.IsSpherical ρ (KGL w n) → (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed ρ (KGL w n), heckeVec ρ (KGL w n) h x = c • x) → ∃ B, HasSatGL w ρ B := by
  first | exact @GlobalTheory.LFun.ExSatGL.exists_hasSatGL | exact GlobalTheory.LFun.ExSatGL.exists_hasSatGL | (intros; apply GlobalTheory.LFun.ExSatGL.exists_hasSatGL <;> assumption)
