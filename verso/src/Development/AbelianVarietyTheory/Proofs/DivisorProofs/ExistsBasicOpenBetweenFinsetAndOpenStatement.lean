import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.exists_basicOpen_between_finset_and_open` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasicOpenBetweenFinsetAndOpen.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_basicOpen_between_finset_and_open' : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  first | exact @GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | exact GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | (intros; apply GlobalTheory.Mum.exists_basicOpen_between_finset_and_open <;> assumption)
