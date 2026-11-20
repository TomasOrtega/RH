import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneSubbundleSplitAtPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankOneSubbundleSplitAtPoints.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.rank_one_subbundle_split_at_points : ∀ (κ : Type) [Field κ] [Infinite κ] (C : Scheme.{0}) [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjOver (strHom κ C) → ∀ (F : C.Modules) (r : ℕ), IsVB F (r + 1) → ∀ S : Set C, S.Finite → ∃ (G : C.Modules) (φ : G ⟶ F), IsVB G 1 ∧ Mono φ ∧ ∀ x ∈ S, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :), ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id := by
  first | exact @GlobalTheory.VB.exists_line_subsheaf_split_at_finite | exact GlobalTheory.VB.exists_line_subsheaf_split_at_finite | (intros; apply GlobalTheory.VB.exists_line_subsheaf_split_at_finite <;> assumption)
