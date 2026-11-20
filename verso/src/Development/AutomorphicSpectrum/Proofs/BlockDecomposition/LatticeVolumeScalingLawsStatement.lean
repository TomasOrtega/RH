import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeScalingLaws
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLatticeVolumeScalingLaws.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.lattice_volume_scaling_laws : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧ (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → vol L = (S.card : ℝ) * vol L') ∧ ∀ (g : GL (Fin d) k) (L : COSub k d), ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub | exact GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub | (intros; apply GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub <;> assumption)
