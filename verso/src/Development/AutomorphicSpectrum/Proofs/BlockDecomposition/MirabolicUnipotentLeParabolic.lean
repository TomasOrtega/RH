import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, if_neg hc, if_neg hrc,
    add_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) : MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  rw [GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff]
  intro b a
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  have ha := a.isLt
  apply one_add_colMat_apply_eq_zero_of_ne_last
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, Fin.val_last] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
    omega

end GlobalTheory.CompanionTheory.LeibPhi
