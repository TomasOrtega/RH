import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta

noncomputable section
open Matrix Formalism.UG

namespace GlobalTheory.InertZeta

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp`. Consider the case `cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]`.
-/
theorem prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.diagonal_apply] split_ifs with h · subst h; exact hf i · exact zero_mem _`.
-/
theorem isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _

/- English proof (translation)
Establish `h0 : ϖ ≠ 0` using `fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm`. Establish `hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L` using `fun m => by show Valued.v (ϖ ^ m) ≤ 1`. Rewrite using `[map_pow, hϖ]`. Conclude with `pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m`. Use `⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1), Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _`. Apply the tactic sequence `exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _`. Conclude with `isInt_diagonal fun i => hpow _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `isInt_diagonal fun i => ?_` and prove the remaining obligations.

Establish `: ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat`. Rewrite using `[← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this]`.

Conclude with `hpow _`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : 0 ≤ d i`.

Simplify using `[h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]`. Simplify using `only [h, if_false, zero_mul, zero_add, one_mul]`. Rewrite using `[← zpow_natCast, ← zpow_add₀ h0]`. Rewrite using `[show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]`. Rewrite using `[Matrix.det_diagonal, map_prod]`.

Simplify using `only [map_pow, hϖ]`. Rewrite using `[Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]`. Use `congr 1`. Use `push_cast`. Simplify using the standard rewrite rules.
-/
theorem hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp

/- English proof (translation)
Introduce `hS L _ _ ϖ n hϖ g hg`. Take `⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩` from `hS L ϖ n hϖ g hg`. Establish `h` using `(hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb`. Rewrite using `[h.len_eq]`. Conclude with `h`.
-/
theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.InertZeta
