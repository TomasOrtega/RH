import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaUnitArg.etaT_isUnitArg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FEtaTildeIsUnitArgAtCmTypePlaces.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.etaTilde_isUnitArg_at_cmType_places : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  first | exact @GlobalTheory.EtaUnitArg.etaT_isUnitArg | exact GlobalTheory.EtaUnitArg.etaT_isUnitArg | (intros; apply GlobalTheory.EtaUnitArg.etaT_isUnitArg <;> assumption)
