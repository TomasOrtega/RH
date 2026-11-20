import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlace
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormCloseToOneOfCloseAbovePlace.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.norm_close_to_one_of_close_above_place : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (M : ℕ), ∃ M' : ℕ, ∀ z : K, (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → w.valuation K (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → v.valuation E (Algebra.norm E z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.NormCont.norm_close_to_one | exact GlobalTheory.NormCompat.NormCont.norm_close_to_one | (intros; apply GlobalTheory.NormCompat.NormCont.norm_close_to_one <;> assumption)
