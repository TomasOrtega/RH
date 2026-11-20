import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp m hdet`. Use `haveI := Fact.mk hp`. Apply the tactic sequence `obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] := ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩`. Rewrite `hdet` using `[Matrix.det_fin_two_of]`. Establish `hdetZ : (a : ZMod p) * d = b * c`.

Use `(ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d → ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)]`. Introduce `k hk h1 h2`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨k, hk, !![a, u; c, v], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_fin_two]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith`. Distinguish the cases in `ha : (a : ZMod p) = 0`. Distinguish the cases in `hc : (c : ZMod p) = 0`.

Use `left`. Take `⟨a', rfl⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha`. Take `⟨c', rfl⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc`. Use `⟨!![a', b; c', d], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_fin_two]`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring`. Use `right`. Use `fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_` and prove the remaining obligations. Rewrite using `[ZMod.natCast_zmod_val]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]`. Use `right`. Use `fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_` and prove the remaining obligations. Rewrite using `[ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]`. Rewrite using `[ZMod.natCast_zmod_val]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem hermite_right_factor_prime_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  intro p hp m hdet
  haveI := Fact.mk hp
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] :=
    ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hdetZ : (a : ZMod p) * d = b * c := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet
    push_cast at this
    linear_combination this
  have fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d →
      ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
    intro k hk h1 h2
    obtain ⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; ring
    obtain ⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h2]; ring
    refine ⟨k, hk, !![a, u; c, v], ?_⟩
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  by_cases ha : (a : ZMod p) = 0
  · by_cases hc : (c : ZMod p) = 0
    · left
      obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha
      obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc
      refine ⟨!![a', b; c', d], ?_⟩
      rw [Matrix.mul_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · right
      refine fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
      · rw [ZMod.natCast_zmod_val]
        calc (d : ZMod p) * (c : ZMod p)⁻¹ * a = (a * d) * (c : ZMod p)⁻¹ := by ring
          _ = b * c * (c : ZMod p)⁻¹ := by rw [hdetZ]
          _ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
      · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · right
    refine fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
    · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rw [ZMod.natCast_zmod_val]
      calc (b : ZMod p) * (a : ZMod p)⁻¹ * c = (b * c) * (a : ZMod p)⁻¹ := by ring
        _ = (a * d) * (a : ZMod p)⁻¹ := by rw [hdetZ]
        _ = d := by rw [mul_comm (a : ZMod p) d, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end GlobalTheory
