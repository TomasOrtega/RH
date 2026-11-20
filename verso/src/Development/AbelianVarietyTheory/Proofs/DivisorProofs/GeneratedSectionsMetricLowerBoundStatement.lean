import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSectionsMetricLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeneratedSectionsMetricLowerBound.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.generated_sections_metric_lower_bound : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (D : Y.Dv) (σ : F →+* ℂ)
    (m : C.Met Y σ D), C.mSmooth Y σ D m → ∀ (k N : ℕ) (s : Fin N → Y.Fn), (∀ i, s i ∈ Y.H0 (k • D)) →
    (∀ x : Y.X, ∃ i, (k • D).GeneratesAt x (s i)) →
    ∃ c : ℝ, 0 < c ∧ ∀ z : Pts Y σ, ∃ j, c ≤ C.pn Y σ _ (C.mPow Y σ D k m) (C.cx Y σ (s j)) z := by
  first | exact @GlobalTheory.ArchLowerBound.exists_pos_le_pn | exact GlobalTheory.ArchLowerBound.exists_pos_le_pn | (intros; apply GlobalTheory.ArchLowerBound.exists_pos_le_pn <;> assumption)
