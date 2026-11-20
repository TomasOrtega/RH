import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelTorsionOfFiniteLengthModElement
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.cokernel_torsion_of_finiteLength_mod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCokernelTorsionOfFiniteLengthModElement.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  first | exact @GlobalTheory.cokernel_torsion_of_finiteLength_mod | exact GlobalTheory.cokernel_torsion_of_finiteLength_mod | (intros; apply GlobalTheory.cokernel_torsion_of_finiteLength_mod <;> assumption)
