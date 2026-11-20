import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNonrepresentedSignatureObstruction.lean&line=509#L509)
-/
theorem _root_.GlobalTheory.T.nonrepresented_signature_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction <;> assumption)
