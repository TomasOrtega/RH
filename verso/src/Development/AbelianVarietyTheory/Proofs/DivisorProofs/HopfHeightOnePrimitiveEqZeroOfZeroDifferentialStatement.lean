import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfHeightOnePrimitiveEqZeroOfZeroDifferential
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHopfHeightOnePrimitiveEqZeroOfZeroDifferential.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → ∀ b : H, cobOne K H b = 0 → dUnit K b = 0 → b = 0 := by
  first | exact @GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | exact GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero | (intros; apply GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero <;> assumption)
