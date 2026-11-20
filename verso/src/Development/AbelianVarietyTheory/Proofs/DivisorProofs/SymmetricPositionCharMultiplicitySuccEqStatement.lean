import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEq
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSymmetricPositionCharMultiplicitySuccEq.lean&line=292#L292)
-/
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ), ρ + k + 2 ≤ r → nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  first | exact @GlobalTheory.FinGL.RootExchange.nPos_succ | exact GlobalTheory.FinGL.RootExchange.nPos_succ | (intros; apply GlobalTheory.FinGL.RootExchange.nPos_succ <;> assumption)
