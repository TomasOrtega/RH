import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open Matrix

namespace GlobalTheory.CompanionTheory.InertZeta

open GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.diagonal_apply] split_ifs with h · exact hf i · exact zero_mem _`.
-/
theorem isInt_diagonal {f : Fin n → L} (hf : ∀ i, f i ∈ Formalism.UG.intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact hf i
  · exact zero_mem _

/- English proof (translation)
Establish `h0 : ϖ ≠ 0` using `fun h => by`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `h1 : Valued.v ϖ ≤ 1`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hpow : ∀ e : ℕ, ϖ ^ e ∈ Formalism.UG.intL L` using `fun e => by`. Express the relevant statement in the definitionally equal form `Valued.v (ϖ ^ e) ≤ 1`. Rewrite using `[map_pow]`. Conclude with `pow_le_one' h1 e`.

Establish `hnum : ∀ i, ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat` using `fun i => by`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `⟨Matrix.diagonal fun i => if 0 ≤ d i then 1 else 0, Matrix.diagonal fun i => if 0 ≤ d i then 0 else 1, Matrix.diagonal fun i => ϖ ^ (-d i).toNat, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `isInt_diagonal fun i => ?_ split_ifs` and prove the remaining obligations. Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `isInt_diagonal fun i => ?_ split_ifs` and prove the remaining obligations. Conclude with `zero_mem _`.

Conclude with `one_mem _`. Conclude with `isInt_diagonal fun i => hpow _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `isInt_diagonal fun i => ?_` and prove the remaining obligations. Rewrite using `[hnum]`.

Conclude with `hpow _`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Distinguish the cases in `h : 0 ≤ d i`.

Establish `: (-d i).toNat = 0` using `by omega`. Simplify using `[h, this]`. Establish `e : ϖ ^ d i * ϖ ^ (-d i).toNat = 1`. Rewrite using `[hnum, show (d i).toNat = 0 by omega, pow_zero]`. Simplify using `[h, e]`.

Rewrite using `[Matrix.det_diagonal, map_prod]`. Simplify using `only [map_pow, hϖ]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem hasLen_diagonal {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal fun i => ϖ ^ d i) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hpow : ∀ e : ℕ, ϖ ^ e ∈ Formalism.UG.intL L := fun e => by
    change Valued.v (ϖ ^ e) ≤ 1
    rw [map_pow]
    exact pow_le_one' h1 e
  have hnum : ∀ i, ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := fun i => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  refine ⟨Matrix.diagonal fun i => if 0 ≤ d i then 1 else 0, Matrix.diagonal fun i => if 0 ≤ d i then 0 else 1,
    Matrix.diagonal fun i => ϖ ^ (-d i).toNat, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact zero_mem _
    · exact one_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    rw [hnum]
    exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : 0 ≤ d i
    · have : (-d i).toNat = 0 := by omega
      simp [h, this]
    · have e : ϖ ^ d i * ϖ ^ (-d i).toNat = 1 := by
        rw [hnum, show (d i).toNat = 0 by omega, pow_zero]
      simp [h, e]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_pow_eq_pow_sum, ← WithZero.exp_nsmul]
    congr 1
    simp

/- English proof (translation)
Introduce `hS L _ _ ϖ n hϖ g hg`. Take `⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩` from `hS L ϖ n hϖ g hg`. Establish `h` using `(hasLen_diagonal hϖ d).mul_mul ha ha' hb hb' ea eb`. Rewrite using `[h.len_eq]`. Conclude with `h`.
-/
theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.CompanionTheory.InertZeta
