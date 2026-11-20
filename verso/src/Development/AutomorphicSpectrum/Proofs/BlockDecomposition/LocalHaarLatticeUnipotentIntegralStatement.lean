import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarLatticeUnipotentIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeightNu.heightNu` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalHaarLatticeUnipotentIntegral.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.local_haar_lattice_unipotent_integral : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (a : GL (Fin n) (AE D)) (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), (∀ v, (lamG v).IsAddHaarMeasure) → ∀ b : hermA D n, PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 = ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.HeightNu.heightNu | exact GlobalTheory.CompanionTheory.HeightNu.heightNu | (intros; apply GlobalTheory.CompanionTheory.HeightNu.heightNu <;> assumption)
