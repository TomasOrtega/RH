import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorization
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryIwahoriFactorization.lean&line=246#L246)
-/
theorem _root_.GlobalTheory.T.unitary_iwahori_factorization : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → ∀ i ∈ IwU σ n, ∃ u ∈ IwU σ n, IsUnipU u ∧ ∃ y ∈ IwU σ n, t⁻¹ * y * t ∈ IwU σ n ∧ i = u * y := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | exact GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | (intros; apply GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact <;> assumption)
