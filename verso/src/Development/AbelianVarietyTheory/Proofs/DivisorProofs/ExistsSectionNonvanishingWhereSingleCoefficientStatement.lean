import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficient
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_sec_sum_nonzero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionNonvanishingWhereSingleCoefficient.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient : ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L), ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) → (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_sum_nonzero | exact GlobalTheory.exists_sec_sum_nonzero | (intros; apply GlobalTheory.exists_sec_sum_nonzero <;> assumption)
