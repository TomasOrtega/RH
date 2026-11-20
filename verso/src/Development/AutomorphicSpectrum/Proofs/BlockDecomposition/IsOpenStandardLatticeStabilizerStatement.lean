import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenStandardLatticeStabilizer
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsOpenStandardLatticeStabilizer.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.isOpen_standard_lattice_stabilizer : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}, IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice | exact GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice <;> assumption)
