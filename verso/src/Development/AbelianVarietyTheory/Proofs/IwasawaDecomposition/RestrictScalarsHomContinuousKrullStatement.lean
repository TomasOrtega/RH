import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrull
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.restrictScalarsHom_continuous_krull` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRestrictScalarsHomContinuousKrull.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuous_restrictScalarsHom' : ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω), Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  first | exact @GlobalTheory.restrictScalarsHom_continuous_krull | exact GlobalTheory.restrictScalarsHom_continuous_krull | (intros; apply GlobalTheory.restrictScalarsHom_continuous_krull <;> assumption)
