import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBasicOpensCoverOfFinite.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.basic_opens_cover_of_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | exact GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | (intros; apply GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top <;> assumption)
