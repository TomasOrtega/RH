import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundary
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LvComm.lv_bd_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviCommuteUnipotentBoundary.lean&line=471#L471)
-/
theorem _root_.GlobalTheory.T.levi_commute_unipotent_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → IsPairA E1 E2 → ∀ p q : Fin n, lev p = lev q →
      (Lv lev E1 E2 p q * bdL (inUU lev) E1 E2 : Module.End ℂ (Cq n V)) = bdL (inUU lev) E1 E2 * Lv lev E1 E2 p q := by
  first | exact @GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | exact GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LvComm.lv_bd_comm <;> assumption)
