import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelIdealOfAppEqZeroField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemKernelIdealOfAppEqZeroField.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G → g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  first | exact @GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | exact GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | (intros; apply GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero <;> assumption)
