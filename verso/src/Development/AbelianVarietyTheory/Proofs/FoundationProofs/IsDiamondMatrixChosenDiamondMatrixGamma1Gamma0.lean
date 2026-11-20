import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma exists_isDiam_of_coprime (N l d : ℕ) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hNl d 1
  have hk1 : Nat.Coprime k N := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkN]
    exact hd
  have hk2 : Nat.Coprime k l := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkl]
    simp
  have hk : Nat.Coprime k (N * l) := Nat.Coprime.mul_right hk1 hk2
  have hg : Int.gcd (k : ℤ) ((N * l : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hk
  have hb := Int.gcd_eq_gcd_ab (k : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  have hdet : (!![Int.gcdA (k : ℤ) ((N * l : ℕ) : ℤ), -Int.gcdB (k : ℤ) ((N * l : ℕ) : ℤ);
      ((N * l : ℕ) : ℤ), (k : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  refine ⟨(⟨_, hdet⟩ : SL(2, ℤ)), Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · simp only [en]
    simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hkN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem isDiam_sgD_of_prime : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N →
    IsDiam N l d (sgD N l d) := by
  intro N l d _ _ hNl hd
  exact Classical.epsilon_spec (exists_isDiam_of_coprime N l d hNl hd)

end GlobalTheory.KZ
