import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjective
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FLabelledTorsionValuesAdditiveKernelSurjective.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  first | exact @GlobalTheory.Ex.arcF_values_add_ker_onto | exact GlobalTheory.Ex.arcF_values_add_ker_onto | (intros; apply GlobalTheory.Ex.arcF_values_add_ker_onto <;> assumption)
