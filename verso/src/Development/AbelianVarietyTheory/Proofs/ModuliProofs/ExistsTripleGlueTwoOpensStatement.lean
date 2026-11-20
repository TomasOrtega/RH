import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsTripleGlueTwoOpens.lean&line=211#L211)
-/
theorem _root_.GlobalTheory.T.exists_triple_glue_two_opens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.TripleGlue.exists_sab_glue | exact GlobalTheory.TripleGlue.exists_sab_glue | (intros; apply GlobalTheory.TripleGlue.exists_sab_glue <;> assumption)
