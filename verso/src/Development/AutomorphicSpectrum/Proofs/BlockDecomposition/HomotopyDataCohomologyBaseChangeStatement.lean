import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHomotopyDataCohomologyBaseChange.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.homotopy_data_cohomology_base_change : ∀ (R A B C H S : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C] [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B) (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B), g ∘ₗ f = 0 → π ∘ₗ j = LinearMap.id → g ∘ₗ j = 0 → π ∘ₗ f = 0 → j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id → Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | exact GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | (intros; apply GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv <;> assumption)
