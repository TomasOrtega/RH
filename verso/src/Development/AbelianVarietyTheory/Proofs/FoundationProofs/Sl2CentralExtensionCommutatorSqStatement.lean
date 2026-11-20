import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSl2CentralExtensionCommutatorSq.lean&line=230#L230)
-/
theorem _root_.GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl : ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  first | exact @GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | exact GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one | (intros; apply GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one <;> assumption)
