import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeNonposTrivialLattice
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FSubDegreeNonposTrivialLattice.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sub_degree_nonpos_trivial_lattice : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial <;> assumption)
