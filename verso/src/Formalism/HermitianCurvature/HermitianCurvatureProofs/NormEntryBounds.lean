import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryMinorBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds

namespace NormEntryBounds

variable {k r : ℕ}

/- English proof (translation)
Unfold `B.gN`. Rewrite using `[show ((2 * r + k + 1 : ℕ) : ℝ) * E = Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2) by`. Rewrite using `[Real.sqrt_sq (by positivity)]]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `hs : ∀ i j, Complex.normSq (g i j) ≤ E ^ 2`.

Introduce `i j`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (h i j) 2`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma gN_le (g : B.Mat k r) (E : ℝ) (hE : 0 ≤ E) (h : ∀ i j, ‖g i j‖ ≤ E) :
    B.gN g ≤ ((2 * r + k + 1 : ℕ) : ℝ) * E := by
  unfold B.gN
  rw [show ((2 * r + k + 1 : ℕ) : ℝ) * E = Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hs : ∀ i j, Complex.normSq (g i j) ≤ E ^ 2 := by
    intro i j; rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (g i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), E ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hs i j))
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/- English proof (translation)
Rewrite using `[gn_Hpk_mulVec]`. Use `split_ifs`. Conclude with `hy _`. Rewrite using `[norm_neg]`. Conclude with `hy _`.

Conclude with `hy _`.
-/
lemma Hpk_mulVec_le (y : Fin (2 * r + k + 1) → ℂ) (X : ℝ) (hy : ∀ p, ‖y p‖ ≤ X) (j : Fin (2 * r + k + 1)) :
    ‖(Hpk k r *ᵥ y) j‖ ≤ X := by
  rw [gn_Hpk_mulVec]
  split_ifs
  · exact hy _
  · rw [norm_neg]; exact hy _
  · exact hy _

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `ht : ∀ p, ‖A i p * M p j‖ ≤ a * b`. Introduce `p`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (ha i p) (hb p j) (norm_nonneg _) (le_trans (norm_nonneg _) (ha i p))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.
-/
lemma mul_entry_le (A M : B.Mat k r) (a b : ℝ) (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖M i j‖ ≤ b)
    (hb0 : 0 ≤ b) (i j : Fin (2 * r + k + 1)) :
    ‖(A * M) i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have ht : ∀ p, ‖A i p * M p j‖ ≤ a * b := by
    intro p
    rw [norm_mul]
    exact mul_le_mul (ha i p) (hb p j) (norm_nonneg _) (le_trans (norm_nonneg _) (ha i p))
  calc ∑ p, ‖A i p * M p j‖ ≤ ∑ _p : Fin (2 * r + k + 1), a * b := Finset.sum_le_sum (fun p _ => ht p)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end NormEntryBounds

open NormEntryBounds

/- English proof (translation)
Introduce `k r z hz`. Establish `hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by positivity`. Take `⟨Zm, hZm⟩ : ∃ Zm : ℝ, Zm = ∑ p, ‖z p‖` from `⟨_, rfl⟩`. Establish `hZm0 : 0 ≤ Zm` using `by rw [hZm]; exact Finset.sum_nonneg (fun p _ => norm_nonneg _)`. Establish `hzp : ∀ p, ‖z p‖ ≤ Zm` using `fun p => by`.

Rewrite using `[hZm]`. Conclude with `Finset.single_le_sum (fun q _ => norm_nonneg (z q)) (Finset.mem_univ p)`. Take `⟨c, hc⟩ : ∃ c : ℂ, c = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ)` from `⟨_, rfl⟩`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = 1 + ‖c‖ * (2 * Zm + 1)` from `⟨_, rfl⟩`. Establish `hA1 : 1 ≤ A` using `by rw [hA]; nlinarith [norm_nonneg c]`.

Take `⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (Nat.factorial r : ℝ)` from `⟨_, rfl⟩`. Establish `hCm1 : 1 ≤ Cm` using `by rw [hCm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)`. Use `⟨((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)), fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨X, hX⟩ : ∃ X, X = C2.mx v` from `⟨_, rfl⟩`. Rewrite using `[← hX]`.

Establish `hX0 : 0 ≤ X` using `by rw [hX]; exact norm_nonneg _`. Establish `hvX : ∀ a b, ‖v a b‖ ≤ X` using `fun a b => by rw [hX]; exact entry_le_mx v a b`. Establish `h1X : 1 ≤ 1 + X` using `by linarith`. Take `⟨ξ, hξ⟩ : ∃ ξ : Fin r → ℂ, ξ = fun a => v a.castSucc (Fin.last r)` from `⟨_, rfl⟩`. Take `⟨vX, hvXe⟩ : ∃ vX : Matrix (Fin r) (Fin r) ℂ, vX = v.submatrix Fin.castSucc Fin.castSucc` from `⟨_, rfl⟩`.

Establish `hvXU : vX ∈ C2.UTset r`. Rewrite using `[hvXe]`. Conclude with `⟨fun i j h => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h), fun i => hv.2 _⟩`. Establish `hτ : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX` using `by rw [hξ, hvXe]; rfl`. Establish `hxi : ∀ p, ‖C2.xiV k r ξ p‖ ≤ X`.

Introduce `p`. Simplify using `only [C2.xiV]`. Use `split_ifs`. Rewrite using `[hξ]`. Conclude with `hvX _ _`.

Rewrite using `[norm_zero]`. Conclude with `hX0`. Establish `hnE : ∀ i j, ‖C2.nEich k r z ξ i j‖ ≤ A * (1 + X) ^ 2`. Introduce `i j`. Simplify using `only [C2.nEich, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, ← hc]`.

Apply the tactic sequence `have h1 : ‖(1 : B.Mat k r) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp`. Establish `hHz` using `Hpk_mulVec_le z Zm hzp j`. Establish `hHx` using `Hpk_mulVec_le (C2.xiV k r ξ) X hxi j`. Establish `hsum : ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) + z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) + 1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ ≤ (2 * Zm + 1) * (1 + X) ^ 2`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Use `(add_le_add (norm_add_le _ _) le_rfl).trans ?_` and prove the remaining obligations. Simplify using `only [norm_neg, norm_mul, norm_star]`. Establish `e1 : ‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ z) j‖ ≤ X * Zm` using `mul_le_mul (hxi i) hHz (norm_nonneg _) hX0`. Establish `e2 : ‖z i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖ ≤ Zm * X` using `mul_le_mul (hzp i) hHx (norm_nonneg _) hZm0`. Establish `e3 : ‖(1 / 2 : ℂ)‖ * (‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖) ≤ 1 * (X * X)`.

Apply `mul_le_mul (by norm_num) (mul_le_mul (hxi i) hHx (norm_nonneg _) hX0) (by positivity) (by norm_num)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `_ ≤ 1 + ‖c‖ * ((2 * Zm + 1) * (1 + X) ^ 2) := add_le_add h1 (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))`. Use `_ ≤ A * (1 + X) ^ 2 := by`. Rewrite using `[hA]; nlinarith [norm_nonneg c, pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) h1X 2, sq_nonneg (1 + X)]`. Establish `hvXb : ∀ a b, ‖vX a b‖ ≤ 1 + X` using `fun a b => by rw [hvXe]; simp only [Matrix.submatrix_apply]; linarith [hvX (Fin.castSucc a) (Fin.castSucc b)]`. Establish `hmE : ∀ i j, ‖C2.mX k r vX i j‖ ≤ Cm * (1 + X) ^ r`.

Establish `hpow1 : 1 ≤ (1 + X) ^ r` using `one_le_pow₀ h1X`. Introduce `i j`. Simplify using `only [C2.mX]`. Use `split_ifs with h1 h2 h3 h4 h5`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ Cm * (1 + X) ^ r := le_mul_of_one_le_left (by positivity) hCm1`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression. Establish `hdet : vXᴴ.det = 1` using `by rw [Matrix.det_conjTranspose, ut_det hvXU, star_one]`.

Use `(inv_entry_le vXᴴ hdet (1 + X) h1X (fun a b => by rw [Matrix.conjTranspose_apply, norm_star]; exact hvXb _ _) _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← hCm]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (Nat.sub_le r 1)) (by positivity)`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression.

Rewrite using `[norm_one]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[norm_zero]`. Check the signs of the components of the expression. Establish `hτE : ∀ i j, ‖C2.tauM k r z v i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (2 * r + 2)`.

Introduce `i j`. Rewrite using `[hτ]`. Use `(mul_entry_le _ _ _ _ hnE hmE (by positivity) i j).trans ?_` and prove the remaining obligations. Establish `key : ((2 * r + k + 1 : ℕ) : ℝ) * (A * (1 + X) ^ 2 * (Cm * (1 + X) ^ r)) = ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (r + 2)` using `by ring`. Rewrite using `[key]`.

Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (by omega)) (by positivity)`. Establish `hgN : B.gN (C2.tauM k r z v) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)) * (1 + X) ^ (2 * r + 2)`. Use `(gN_le _ _ (by positivity) hτE).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hτG : C2.tauM k r z v ∈ B.GV k r` using `((c2_tau_mem k r z hz v hv).1).1`.

Use `⟨hgN, ?_⟩` and prove the remaining obligations. Rewrite using `[(norm_of_inverse k r _ hτG).1]`. Conclude with `hgN`.
-/
theorem tau_norm_bound : C2.TauBound := by
  intro k r z hz
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨Zm, hZm⟩ : ∃ Zm : ℝ, Zm = ∑ p, ‖z p‖ := ⟨_, rfl⟩
  have hZm0 : 0 ≤ Zm := by rw [hZm]; exact Finset.sum_nonneg (fun p _ => norm_nonneg _)
  have hzp : ∀ p, ‖z p‖ ≤ Zm := fun p => by
    rw [hZm]; exact Finset.single_le_sum (fun q _ => norm_nonneg (z q)) (Finset.mem_univ p)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + ‖c‖ * (2 * Zm + 1) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [norm_nonneg c]
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (Nat.factorial r : ℝ) := ⟨_, rfl⟩
  have hCm1 : 1 ≤ Cm := by rw [hCm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)), fun v hv => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, X = C2.mx v := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hvX : ∀ a b, ‖v a b‖ ≤ X := fun a b => by rw [hX]; exact entry_le_mx v a b
  have h1X : 1 ≤ 1 + X := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin r → ℂ, ξ = fun a => v a.castSucc (Fin.last r) := ⟨_, rfl⟩
  obtain ⟨vX, hvXe⟩ : ∃ vX : Matrix (Fin r) (Fin r) ℂ, vX = v.submatrix Fin.castSucc Fin.castSucc := ⟨_, rfl⟩
  have hvXU : vX ∈ C2.UTset r := by
    rw [hvXe]; exact ⟨fun i j h => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h), fun i => hv.2 _⟩
  have hτ : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := by rw [hξ, hvXe]; rfl
  have hxi : ∀ p, ‖C2.xiV k r ξ p‖ ≤ X := by
    intro p; simp only [C2.xiV]; split_ifs
    · rw [hξ]; exact hvX _ _
    · rw [norm_zero]; exact hX0

  have hnE : ∀ i j, ‖C2.nEich k r z ξ i j‖ ≤ A * (1 + X) ^ 2 := by
    intro i j
    simp only [C2.nEich, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply,
      Pi.star_apply, smul_eq_mul, ← hc]
    have h1 : ‖(1 : B.Mat k r) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
    have hHz := Hpk_mulVec_le z Zm hzp j
    have hHx := Hpk_mulVec_le (C2.xiV k r ξ) X hxi j
    have hsum : ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) + z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
        1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ ≤ (2 * Zm + 1) * (1 + X) ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      simp only [norm_neg, norm_mul, norm_star]
      have e1 : ‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ z) j‖ ≤ X * Zm := mul_le_mul (hxi i) hHz (norm_nonneg _) hX0
      have e2 : ‖z i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖ ≤ Zm * X := mul_le_mul (hzp i) hHx (norm_nonneg _) hZm0
      have e3 : ‖(1 / 2 : ℂ)‖ * (‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖) ≤ 1 * (X * X) := by
        apply mul_le_mul (by norm_num) (mul_le_mul (hxi i) hHx (norm_nonneg _) hX0) (by positivity) (by norm_num)
      nlinarith
    calc _ ≤ ‖(1 : B.Mat k r) i j‖ + ‖c‖ * ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) +
            z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
            1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul]
      _ ≤ 1 + ‖c‖ * ((2 * Zm + 1) * (1 + X) ^ 2) := add_le_add h1 (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
      _ ≤ A * (1 + X) ^ 2 := by
          rw [hA]; nlinarith [norm_nonneg c, pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) h1X 2, sq_nonneg (1 + X)]

  have hvXb : ∀ a b, ‖vX a b‖ ≤ 1 + X := fun a b => by rw [hvXe]; simp only [Matrix.submatrix_apply]; linarith [hvX (Fin.castSucc a) (Fin.castSucc b)]
  have hmE : ∀ i j, ‖C2.mX k r vX i j‖ ≤ Cm * (1 + X) ^ r := by
    have hpow1 : 1 ≤ (1 + X) ^ r := one_le_pow₀ h1X
    intro i j
    simp only [C2.mX]
    split_ifs with h1 h2 h3 h4 h5
    · calc ‖vX _ _‖ ≤ 1 + X := hvXb _ _
        _ ≤ (1 + X) ^ r := by
            calc 1 + X = (1 + X) ^ 1 := (pow_one _).symm
              _ ≤ (1 + X) ^ r := pow_le_pow_right₀ h1X (by omega)
        _ ≤ Cm * (1 + X) ^ r := le_mul_of_one_le_left (by positivity) hCm1
    · rw [norm_zero]; positivity
    · have hdet : vXᴴ.det = 1 := by rw [Matrix.det_conjTranspose, ut_det hvXU, star_one]
      refine (inv_entry_le vXᴴ hdet (1 + X) h1X
        (fun a b => by rw [Matrix.conjTranspose_apply, norm_star]; exact hvXb _ _) _ _).trans ?_
      rw [← hCm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (Nat.sub_le r 1)) (by positivity)
    · rw [norm_zero]; positivity
    · rw [norm_one]; nlinarith
    · rw [norm_zero]; positivity
  have hτE : ∀ i j, ‖C2.tauM k r z v i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (2 * r + 2) := by
    intro i j
    rw [hτ]
    refine (mul_entry_le _ _ _ _ hnE hmE (by positivity) i j).trans ?_
    have key : ((2 * r + k + 1 : ℕ) : ℝ) * (A * (1 + X) ^ 2 * (Cm * (1 + X) ^ r)) =
        ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (r + 2) := by ring
    rw [key]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (by omega)) (by positivity)
  have hgN : B.gN (C2.tauM k r z v) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)) *
      (1 + X) ^ (2 * r + 2) := by
    refine (gN_le _ _ (by positivity) hτE).trans (le_of_eq ?_)
    ring
  have hτG : C2.tauM k r z v ∈ B.GV k r := ((c2_tau_mem k r z hz v hv).1).1
  refine ⟨hgN, ?_⟩
  rw [(norm_of_inverse k r _ hτG).1]
  exact hgN

end Formalism.FourierDecayAlt.P
