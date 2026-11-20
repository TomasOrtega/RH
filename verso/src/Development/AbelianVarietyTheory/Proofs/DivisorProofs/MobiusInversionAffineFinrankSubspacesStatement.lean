import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusInversionAffineFinrankSubspaces

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMobiusInversionAffineFinrankSubspaces.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.mobiusInversion_affine_finrank_subspaces : ∀ (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ), 0 < Module.finrank K U → (∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 = c₀ + c * (Module.finrank K A : ℂ)) → G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.moebius_affine_finrank | exact GlobalTheory.CuspGL.moebius_affine_finrank | (intros; apply GlobalTheory.CuspGL.moebius_affine_finrank <;> assumption)
