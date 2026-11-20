import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCardPadicAlgClPadicComplexEqComplex.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex : ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧ Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  first | exact @GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | exact GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | (intros; apply GlobalTheory.PadicCard.card_padicAlgCl_padicComplex <;> assumption)
