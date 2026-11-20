import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeLocInt

open Matrix

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `hx`, the goal using `[← WithZero.exp_log h0]`. Rewrite `hx` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Conclude with `WithZero.exp_le_exp.2 (by omega)`.
-/
theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at hx ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
  exact WithZero.exp_le_exp.2 (by omega)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hM i l) (hN l j)`.
-/
theorem int_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) :
    ∀ i j, Valued.v ((M * N) i j) ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun l _ => ?_)
  rw [map_mul]
  exact mul_le_one' (hM i l) (hN l j)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_lt _ one_ne_zero (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hM i l)) (hN l j)`.
-/
theorem small_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) < 1) :
    ∀ i j, Valued.v ((M * N) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero (fun l _ => ?_)
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hM i l)) (hN l j)

/- English proof (translation)
Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hDD : Formalism.UG.diagJ n ϖ⁻¹ k * Formalism.UG.diagJ n ϖ k = 1`.

Unfold `Formalism.UG.diagJ`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp [hϖ0]`. Establish `hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Apply `Units.inv_eq_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[hg]`. Establish `e : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K)) = ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K …`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul]`. Establish `key : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) = ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin …`.

Rewrite using `[Matrix.mul_sub, Units.inv_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD, add_sub_cancel]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hsub' : ∀ i j, Valued.v (((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K)) i j) < 1`. Introduce `i j`. Rewrite using `[Matrix.sub_apply, Valuation.map_sub_swap]`.

Conclude with `hsub i j`. Establish `hN` using `small_mul hai hsub'`. Establish `hX : ∀ i j, Valued.v ((1 + Formalism.UG.diagJ n ϖ⁻¹ k * (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) * Formalism.UG.diagJ n ϖ k) i j) ≤ 1`. Introduce `i j`. Rewrite using `[Matrix.add_apply]`.

Apply `Valuation.map_add_le` to reduce the goal to its premises. Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Simplify using `only [Formalism.UG.diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[map_mul, map_mul]`. Establish `h1 : Valued.v (if (i : ℕ) < k then ϖ⁻¹ else 1) ≤ WithZero.exp (1 : ℤ)` using `by split_ifs`.

Rewrite using `[map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]`. Rewrite using `[map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Establish `h2 : Valued.v (if (j : ℕ) < k then ϖ else 1) ≤ 1` using `by split_ifs`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Evaluate the numerical expressions. Rewrite using `[map_one]`. Establish `h3` using `le_exp_neg_one_of_lt (hN i j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, hinv, hg', key]`.

Conclude with `int_mul (int_mul hbi hX) hb'`.
-/
theorem inv_mul_int_of_left_congr {n : ℕ} (ϖ : K) (k : ℕ)
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a a' b b' g g' : GL (Fin n) K)
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hsub : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) K) i j -
      (a' : Matrix (Fin n) (Fin n) K) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K))
    (hg' : (g' : Matrix (Fin n) (Fin n) K) =
      (a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hDD : Formalism.UG.diagJ n ϖ⁻¹ k * Formalism.UG.diagJ n ϖ k = 1 := by
    unfold Formalism.UG.diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ0]
  have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hg]
    have e : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K)) =
        ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K)) *
        Formalism.UG.diagJ n ϖ k) * (b : Matrix (Fin n) (Fin n) K) := by
      simp only [Matrix.mul_assoc]
    rw [e, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul]
  have key : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) * (b' : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD,
      add_sub_cancel]
    simp only [Matrix.mul_assoc]
  have hsub' : ∀ i j, Valued.v (((a' : Matrix (Fin n) (Fin n) K) -
      (a : Matrix (Fin n) (Fin n) K)) i j) < 1 := by
    intro i j; rw [Matrix.sub_apply, Valuation.map_sub_swap]; exact hsub i j
  have hN := small_mul hai hsub'
  have hX : ∀ i j, Valued.v ((1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) i j) ≤ 1 := by
    intro i j
    rw [Matrix.add_apply]
    apply Valuation.map_add_le
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · simp only [Formalism.UG.diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [map_mul, map_mul]
      have h1 : Valued.v (if (i : ℕ) < k then ϖ⁻¹ else 1) ≤ WithZero.exp (1 : ℤ) := by
        split_ifs
        · rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
        · rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
      have h2 : Valued.v (if (j : ℕ) < k then ϖ else 1) ≤ 1 := by
        split_ifs
        · rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
        · rw [map_one]
      have h3 := le_exp_neg_one_of_lt (hN i j)
      calc _ ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' h1 h3) h2
        _ = 1 := by rw [mul_one, ← WithZero.exp_add]; simp
  rw [Units.val_mul, hinv, hg', key]
  exact int_mul (int_mul hbi hX) hb'

end GlobalTheory.HeckeLocInt

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'`. Conclude with `HeckeLocInt.inv_mul_int_of_left_congr ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'`.
-/
theorem hecke_loc_inv_mul_int : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  intro F _ _ v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'
  exact HeckeLocInt.inv_mul_int_of_left_congr ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'

end GlobalTheory
