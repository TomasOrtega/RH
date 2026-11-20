import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeUnifVal.at_val_and_unr_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUnramifiedHeckeCharIdeleValueUniformiser.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_idele_value_uniformiser : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  first | exact @GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | exact GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | (intros; apply GlobalTheory.HeckeUnifVal.at_val_and_unr_iff <;> assumption)
