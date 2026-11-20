import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianIdempotentEqIsometryMulConjTranspose

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IsoFrame

/- English proof (translation)
Establish `h5 : A * S * A * S * A = A * S * A`. Rewrite using `[show A * S * A * S * A = A * (S * A * S) * A by noncomm_ring, hSAS]`. Establish `key : (A - A * S * A) * (A - A * S * A) = (A - A * S * A) + (A - A * S * A)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, key, ← two_smul ℂ, smul_smul, smul_smul]`.

Evaluate the numerical expressions.
-/
private theorem half_smul_sub_mul_mul_mul_self {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (hAA : A * A = A + A)
    (hSAS : S * A * S = S) :
    ((1 / 2 : ℂ) • (A - A * S * A)) * ((1 / 2 : ℂ) • (A - A * S * A)) =
      (1 / 2 : ℂ) • (A - A * S * A) := by
  have h5 : A * S * A * S * A = A * S * A := by
    rw [show A * S * A * S * A = A * (S * A * S) * A by noncomm_ring, hSAS]
  have key : (A - A * S * A) * (A - A * S * A) = (A - A * S * A) + (A - A * S * A) := by
    calc (A - A * S * A) * (A - A * S * A)
        = A * A - (A * A) * S * A - A * S * (A * A) + A * S * (A * A) * S * A := by noncomm_ring
      _ = (A + A) - (A + A) * S * A - A * S * (A + A) + A * S * (A + A) * S * A := by rw [hAA]
      _ = (A + A) - (A * S * A + A * S * A) - (A * S * A + A * S * A)
            + (A * S * A * S * A + A * S * A * S * A) := by noncomm_ring
      _ = (A - A * S * A) + (A - A * S * A) := by rw [h5]; abel
  rw [Matrix.smul_mul, Matrix.mul_smul, key, ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

/- English proof (translation)
Establish `hA : ∀ i k, (T i)ᴴ * (1 + J) * T k = (T i)ᴴ * T k`. Introduce `i k`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h3, add_zero]`. Establish `hTS : ∀ i, (T i)ᴴ * (1 + J) * (∑ k, T k * (T k)ᴴ) = (T i)ᴴ`. Introduce `i`.

Rewrite using `[Matrix.mul_sum, Finset.sum_eq_single i]`. Rewrite using `[← Matrix.mul_assoc, hA, h1, Matrix.one_mul]`. Introduce `k _ hk`. Rewrite using `[← Matrix.mul_assoc, hA, h2 i k (Ne.symm hk), Matrix.zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Establish `hSAS : (∑ k, T k * (T k)ᴴ) * (1 + J) * (∑ k, T k * (T k)ᴴ) = ∑ k, T k * (T k)ᴴ`. Rewrite using `[Matrix.mul_assoc, Matrix.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (T k)ᴴ, hTS]`.

Establish `hAA : (1 + J) * (1 + J) = (1 + J) + (1 + J)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJJ]`. Normalize the expressions using the abelian group laws. Establish `hJA : J * (1 + J) = 1 + J`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, hJJ, add_comm]`.

Establish `hRR` using `half_smul_sub_mul_mul_mul_self (1 + J) (∑ k, T k * (T k)ᴴ) hAA hSAS`. Establish `hAh : (1 + J)ᴴ = 1 + J`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJh]`. Establish `hSh : (∑ k, T k * (T k)ᴴ)ᴴ = ∑ k, T k * (T k)ᴴ`. Simplify using `only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`.

Establish `hRh : ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))ᴴ = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAh, hSh, ← Matrix.mul_assoc]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `htrS : Matrix.trace ((1 + J) * (∑ k, T k * (T k)ᴴ)) = ∑ k, (j k : ℂ)`.

Rewrite using `[Matrix.mul_sum, Matrix.trace_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, h1, Matrix.trace_one, Fintype.card_fin]`. Establish `htrR : Matrix.trace ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = (p : ℂ) - ∑ i, (j i : ℂ)`. Rewrite using `[Matrix.trace_smul, Matrix.trace_sub, hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAA, Matrix.add_mul, Matrix.trace_add, htrS]`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, P, hPP, hPR⟩` from `GlobalTheory.hermitian_idempotent_eq_isometry_mul_conjTranspose n _ hRh hRR`. Establish `hr : (r : ℂ) = (p : ℂ) - ∑ i, (j i : ℂ)`. Rewrite using `[← htrR, ← hPR, Matrix.trace_mul_comm, hPP, Matrix.trace_one, Fintype.card_fin]`.

Establish `hr' : r = p - ∑ i, j i`. Establish `hc : ((r + ∑ i, j i : ℕ) : ℂ) = (p : ℂ)` using `by push_cast; rw [hr]; ring`. Establish `h' : r + ∑ i, j i = p` using `by exact_mod_cast hc`. Use linear arithmetic over natural numbers and integers. Substitute `hr'` using the available equality.

Establish `hRP : (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) * P = P`. Rewrite using `[← hPR, Matrix.mul_assoc, hPP, Matrix.mul_one]`. Establish `hTR : ∀ i, (T i)ᴴ * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = 0`. Introduce `i`. Rewrite using `[Matrix.mul_smul, Matrix.mul_sub]`.

Simplify using `only [← Matrix.mul_assoc, hTS, sub_self, smul_zero]`. Establish `hJR : J * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))`. Rewrite using `[Matrix.mul_smul, Matrix.mul_sub]`. Simplify using `only [← Matrix.mul_assoc, hJA]`. Use `⟨P, fun i => ?_, hPP, ?_, hPR⟩` and prove the remaining obligations.

Rewrite using `[← hRP, ← Matrix.mul_assoc, hTR i, Matrix.zero_mul]`. Rewrite using `[← hRP, ← Matrix.mul_assoc, hJR]`.
-/
theorem exists_eigenframe {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J) (p : ℕ)
    (hp : Matrix.trace (1 + J) = 2 * (p : ℂ)) {a : ℕ} (j : Fin a → ℕ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) :
    ∃ P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ, (∀ i, (T i)ᴴ * P = 0) ∧ Pᴴ * P = 1 ∧ J * P = P ∧
      P * Pᴴ = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by

  have hA : ∀ i k, (T i)ᴴ * (1 + J) * T k = (T i)ᴴ * T k := by
    intro i k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h3, add_zero]
  have hTS : ∀ i, (T i)ᴴ * (1 + J) * (∑ k, T k * (T k)ᴴ) = (T i)ᴴ := by
    intro i
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, hA, h1, Matrix.one_mul]
    · intro k _ hk
      rw [← Matrix.mul_assoc, hA, h2 i k (Ne.symm hk), Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hSAS : (∑ k, T k * (T k)ᴴ) * (1 + J) * (∑ k, T k * (T k)ᴴ) = ∑ k, T k * (T k)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T k)ᴴ, hTS]
  have hAA : (1 + J) * (1 + J) = (1 + J) + (1 + J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJJ]; abel
  have hJA : J * (1 + J) = 1 + J := by
    rw [Matrix.mul_add, Matrix.mul_one, hJJ, add_comm]

  have hRR := half_smul_sub_mul_mul_mul_self (1 + J) (∑ k, T k * (T k)ᴴ) hAA hSAS
  have hAh : (1 + J)ᴴ = 1 + J := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJh]
  have hSh : (∑ k, T k * (T k)ᴴ)ᴴ = ∑ k, T k * (T k)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hRh : ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))ᴴ
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hAh, hSh, ← Matrix.mul_assoc]
    congr 1
    simp

  have htrS : Matrix.trace ((1 + J) * (∑ k, T k * (T k)ᴴ)) = ∑ k, (j k : ℂ) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, h1, Matrix.trace_one,
      Fintype.card_fin]
  have htrR : Matrix.trace ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_sub, hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAA,
      Matrix.add_mul, Matrix.trace_add, htrS]
    simp only [smul_eq_mul]; ring
  obtain ⟨r, P, hPP, hPR⟩ := GlobalTheory.hermitian_idempotent_eq_isometry_mul_conjTranspose n _ hRh hRR
  have hr : (r : ℂ) = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [← htrR, ← hPR, Matrix.trace_mul_comm, hPP, Matrix.trace_one, Fintype.card_fin]
  have hr' : r = p - ∑ i, j i := by
    have hc : ((r + ∑ i, j i : ℕ) : ℂ) = (p : ℂ) := by push_cast; rw [hr]; ring
    have h' : r + ∑ i, j i = p := by exact_mod_cast hc
    omega
  subst hr'
  have hRP : (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) * P = P := by
    rw [← hPR, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hTR : ∀ i, (T i)ᴴ * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = 0 := by
    intro i
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hTS, sub_self, smul_zero]
  have hJR : J * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hJA]
  refine ⟨P, fun i => ?_, hPP, ?_, hPR⟩
  · rw [← hRP, ← Matrix.mul_assoc, hTR i, Matrix.zero_mul]
  · rw [← hRP, ← Matrix.mul_assoc, hJR]

/- English proof (translation)
Introduce `n ε p q hp hq a j T h1 h2 h3`. Establish `hJdef : Formalism.REAL.Jm ε = Matrix.diagonal (fun b => if ε b = true then (1 : ℂ) else -1)`. Unfold `Formalism.REAL.Jm`. Apply the tactic sequence `try rfl`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`.

Rewrite using `[hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext b; split_ifs <;> norm_num`. Establish `hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε`. Rewrite using `[hJdef, Matrix.diagonal_conjTranspose]`. Apply the tactic sequence `congr 1; funext b; simp only [Pi.star_apply]; split_ifs <;> simp`.

Establish `htp : Matrix.trace (1 + Formalism.REAL.Jm ε) = 2 * (p : ℂ)`. Rewrite using `[hJdef, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.trace_diagonal]`. Use `(Finset.sum_congr rfl (g := fun b => if ε b = true then (2 : ℂ) else 0) fun b _ => ?_).trans ?_` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Apply the tactic sequence `cases ε b <;> norm_num`.

Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `htq : Matrix.trace (1 + -Formalism.REAL.Jm ε) = 2 * (q : ℂ)`. Rewrite using `[hJdef, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.diagonal_add, Matrix.trace_diagonal]`. Use `(Finset.sum_congr rfl (g := fun b => if ε b = false then (2 : ℂ) else 0) fun b _ => ?_).trans ?_` and prove the remaining obligations.

Apply the tactic sequence `try dsimp only`. Apply the tactic sequence `cases ε b <;> norm_num`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hq]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨P, hP0, hPP, hJP, hPR⟩` from `exists_eigenframe _ hJJ hJh p htp j T h1 h2 h3`.

Establish `h3' : ∀ i k, (T i)ᴴ * (-Formalism.REAL.Jm ε) * T k = 0`. Introduce `i k`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, h3, neg_zero]`. Take `⟨Q, hQ0, hQQ, hJQ, hQR⟩` from `exists_eigenframe (-Formalism.REAL.Jm ε) (by rw [neg_mul_neg, hJJ]) (by rw [Matrix.conjTranspose_neg, hJh]) q htq j T h1 h2 h3'`. Use `⟨P, Q, hP0, hQ0, hPP, hQQ, hJP, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hJQ` using `[Matrix.neg_mul, neg_eq_iff_eq_neg]`. Conclude with `hJQ`. Establish `hsum : (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) = (∑ i, T i * (T i)ᴴ) + Formalism.REAL.Jm ε * (∑ i, T i * (T i)ᴴ) * Formalism.REAL.Jm ε`. Rewrite using `[Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[hsum, hPR, hQR]`. Generalize the expression as in `(∑ i, T i * (T i)ᴴ) = S`. Generalize the expression as in `Formalism.REAL.Jm ε = J`. Establish `hX : ((1 + J) - (1 + J) * S * (1 + J)) + ((1 + -J) - (1 + -J) * S * (1 + -J)) = (1 - S - J * S * J) + (1 - S - J * S * J)` using `by noncomm_ring`. Rewrite using `[add_assoc (S + J * S * J), ← smul_add, hX, ← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem complete_isotropic_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  intro n ε p q hp hq a j T h1 h2 h3

  have hJdef : Formalism.REAL.Jm ε = Matrix.diagonal (fun b => if ε b = true then (1 : ℂ) else -1) := by
    unfold Formalism.REAL.Jm
    try rfl
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext b; split_ifs <;> norm_num
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [hJdef, Matrix.diagonal_conjTranspose]
    congr 1; funext b; simp only [Pi.star_apply]; split_ifs <;> simp
  have htp : Matrix.trace (1 + Formalism.REAL.Jm ε) = 2 * (p : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = true then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hp]; ring
  have htq : Matrix.trace (1 + -Formalism.REAL.Jm ε) = 2 * (q : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = false then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hq]; ring

  obtain ⟨P, hP0, hPP, hJP, hPR⟩ := exists_eigenframe _ hJJ hJh p htp j T h1 h2 h3
  have h3' : ∀ i k, (T i)ᴴ * (-Formalism.REAL.Jm ε) * T k = 0 := by
    intro i k; rw [Matrix.mul_neg, Matrix.neg_mul, h3, neg_zero]
  obtain ⟨Q, hQ0, hQQ, hJQ, hQR⟩ := exists_eigenframe (-Formalism.REAL.Jm ε)
    (by rw [neg_mul_neg, hJJ]) (by rw [Matrix.conjTranspose_neg, hJh]) q htq j T h1 h2 h3'
  refine ⟨P, Q, hP0, hQ0, hPP, hQQ, hJP, ?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_iff_eq_neg] at hJQ; exact hJQ
  · have hsum : (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε))
        = (∑ i, T i * (T i)ᴴ) + Formalism.REAL.Jm ε * (∑ i, T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
      rw [Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum, hPR, hQR]
    generalize (∑ i, T i * (T i)ᴴ) = S
    generalize Formalism.REAL.Jm ε = J

    have hX : ((1 + J) - (1 + J) * S * (1 + J)) + ((1 + -J) - (1 + -J) * S * (1 + -J))
        = (1 - S - J * S * J) + (1 - S - J * S * J) := by noncomm_ring
    rw [add_assoc (S + J * S * J), ← smul_add, hX, ← two_smul ℂ, smul_smul,
      show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
    abel

end GlobalTheory.IsoFrame
