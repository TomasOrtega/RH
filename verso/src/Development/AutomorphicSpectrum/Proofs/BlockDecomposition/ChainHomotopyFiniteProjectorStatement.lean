import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjector
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FChainHomotopyFiniteProjector.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.chain_homotopy_finite_projector : ∀ {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R),
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  first | exact @GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | exact GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | (intros; apply GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation <;> assumption)
