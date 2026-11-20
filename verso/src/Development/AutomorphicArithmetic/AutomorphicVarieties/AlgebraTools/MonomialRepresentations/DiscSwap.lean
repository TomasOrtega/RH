import Mathlib

open Polynomial Matrix

/- English proof (translation)
Unfold `Matrix.charpoly`. Rewrite using `[charmatrix_fromBlocks]`. Establish `hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X]))`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[charmatrix_apply]`. Simplify using `[charmatrix_apply, diagonal_apply_ne _ h]`. Rewrite using `[hcz]`. Generalize the expression as in `hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S`.

Generalize the expression as in `hP' : P.map C = P'`. Generalize the expression as in `hQ' : Q.map C = Q'`. Establish `hcomm : S * P' = P' * S`. Substitute `hS` using the available equality. Use extensionality with `i j`.

Simplify using `[mul_comm]`. Establish `hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P')`. Rewrite using `[fromBlocks_multiply, fromBlocks_inj]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[hcomm, neg_mul, add_neg_cancel]`. Simplify using the standard rewrite rules. Rewrite using `[neg_mul, add_comm, sub_eq_add_neg]`. Establish `hdet` using `congrArg det hprod`. Rewrite `hdet` using `[det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]`.

Establish `hSd : det S = X ^ 2`. Substitute `hS` using the available equality. Simplify using `[det_diagonal, Fin.prod_univ_two, sq]`. Rewrite `hdet` using `[det_mul, hSd]`. Establish `hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0`.

Conclude with `mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)`. Establish `hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P')`. Apply `mul_right_cancel₀ hX` to reduce the goal to its premises. Rewrite using `[hdet]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hG, det_fin_two]`. Substitute `hS hP' hQ'` using the available equality. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem charpoly_fromBlocks_antidiagonal_fin_two {F : Type} [Field F] (P Q : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks 0 P Q 0).charpoly = X ^ 4 - C ((Q * P) 0 0 + (Q * P) 1 1) * X ^ 2
      + C ((Q * P) 0 0 * (Q * P) 1 1 - (Q * P) 0 1 * (Q * P) 1 0) := by
  unfold Matrix.charpoly
  rw [charmatrix_fromBlocks]
  have hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X])) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [charmatrix_apply]
    · simp [charmatrix_apply, diagonal_apply_ne _ h]
  rw [hcz]
  generalize hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S
  generalize hP' : P.map C = P'
  generalize hQ' : Q.map C = Q'
  have hcomm : S * P' = P' * S := by
    subst hS
    ext i j
    simp [mul_comm]
  have hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S
      = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P') := by
    rw [fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcomm, neg_mul, add_neg_cancel]
    · simp
    · rw [neg_mul, add_comm, sub_eq_add_neg]
  have hdet := congrArg det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  have hSd : det S = X ^ 2 := by
    subst hS
    simp [det_diagonal, Fin.prod_univ_two, sq]
  rw [det_mul, hSd] at hdet
  have hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P') := by
    apply mul_right_cancel₀ hX
    rw [hdet]
    ring
  rw [hG, det_fin_two]
  subst hS hP' hQ'
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/- English proof (translation)
Establish `h4 : (4 : F) ≠ 0`. Rewrite using `[show (4 : F) = 2 * 2 by norm_num]`. Conclude with `mul_ne_zero h2 h2`. Establish `hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0`. Use `mul_ne_zero (mul_ne_zero h4 hd) ?_` and prove the remaining obligations.

Rewrite using `[show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]`. Conclude with `mul_ne_zero (neg_ne_zero.2 h2) he`. Establish `hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X`. Rewrite using `[derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]`. Evaluate the numerical expressions.

Simplify using `only [map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2`. Simplify using `only [map_mul, map_sub, map_pow, map_ofNat]`. Establish `key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d) + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X) = C (4 * d * (8 * d - 2 * a ^ 2))`.

Rewrite using `[map_mul, map_mul, hCe]`. Simplify using `only [map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Unfold `Polynomial.Separable IsCoprime`. Use `⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)), C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩` and prove the remaining obligations.

Rewrite using `[hder]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem separable_biquadratic_of_ne_zero_of_discrim_ne_zero {F : Type} [Field F] (a d : F) (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    (he : a ^ 2 - 4 * d ≠ 0) : (X ^ 4 - C a * X ^ 2 + C d : F[X]).Separable := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 hd) ?_
    rw [show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]
    exact mul_ne_zero (neg_ne_zero.2 h2) he
  have hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]
    norm_num
    simp only [map_ofNat]
    ring
  have hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2 := by
    simp only [map_mul, map_sub, map_pow, map_ofNat]
  have key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d)
      + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X)
      = C (4 * d * (8 * d - 2 * a ^ 2)) := by
    rw [map_mul, map_mul, hCe]
    simp only [map_ofNat]
    ring
  unfold Polynomial.Separable IsCoprime
  refine ⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)),
    C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩
  rw [hder]
  calc _ = C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * C (4 * d * (8 * d - 2 * a ^ 2)) := by rw [← key]; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hk, C_1]

/- English proof (translation)
Introduce `N`. Establish `h01 : (0 : Fin 2) < 1` using `by decide`. Take `⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n` from `⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩`. Take `⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m` from `⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩`. Use `set f := algebraMap K (RatFunc K) with hf`.

Use `set Y : RatFunc K := RatFunc.X with hY`. Establish `hY0 : Y ≠ 0` using `RatFunc.X_ne_zero`. Establish `hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n` using `by rw [hn, zpow_add₀ hY0, zpow_natCast]`. Establish `hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m` using `by rw [hm, zpow_add₀ hY0, zpow_natCast]`. Establish `hu : Y ^ w₁ 1 ≠ 0` using `zpow_ne_zero _ hY0`.

Establish `hv : Y ^ w₂ 1 ≠ 0` using `zpow_ne_zero _ hY0`. Establish `e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0) + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0)`. Apply the tactic sequence `simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring`. Establish `e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1) + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1)`. Apply the tactic sequence `simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring`.

Establish `e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0) + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0)`. Apply the tactic sequence `simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring`. Establish `e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1) + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1)`. Apply the tactic sequence `simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring`. Establish `hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m)`.

Rewrite using `[e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]`. Simplify using `only [map_mul, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdet]`.

Use `mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)` and prove the remaining obligations. Conclude with `(map_ne_zero f).2 (mul_ne_zero hcd hbd)`. Use `set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m) + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol`. Establish `hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol`. Rewrite using `[hdet, e00, e11, hA, hB, hPol, hq]`.

Simplify using `only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree < n + m`. Establish `h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree ≤ max n m`. Use `natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_` and prove the remaining obligations.

Conclude with `(natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)`. Conclude with `(natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)`. Rewrite using `[natDegree_C]`. Conclude with `Nat.zero_le _`. Use linear arithmetic over natural numbers and integers.

Establish `hqd : q.natDegree = n + m`. Apply the tactic sequence `rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]`. Conclude with `hrest`. Establish `hPol0 : Pol ≠ 0`. Introduce `h0`.

Establish `hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m)` using `sub_eq_zero.1 (hPol ▸ h0)`. Use `congrArg natDegree hsq` as an intermediate fact. Rewrite `this` using `[natDegree_pow, hqd]`. Establish `hle` using `natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hkey]`. Use `mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0`.
-/
private theorem discSwap_lemma_3 {K : Type} [Field K] (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ)
    (hw₁ : StrictAnti w₁) (hw₂ : StrictAnti w₂) (hb : b 0 0 ≠ 0) (hc : c 0 0 ≠ 0)
    (hbd : b.det ≠ 0) (hcd : c.det ≠ 0) :
    let N := (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) *
      (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
    N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 ∧
      (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) ≠ 0 := by
  intro N
  have h01 : (0 : Fin 2) < 1 := by decide
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n :=
    ⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m :=
    ⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩
  set f := algebraMap K (RatFunc K) with hf
  set Y : RatFunc K := RatFunc.X with hY
  have hY0 : Y ≠ 0 := RatFunc.X_ne_zero
  have hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n := by rw [hn, zpow_add₀ hY0, zpow_natCast]
  have hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m := by rw [hm, zpow_add₀ hY0, zpow_natCast]
  have hu : Y ^ w₁ 1 ≠ 0 := zpow_ne_zero _ hY0
  have hv : Y ^ w₂ 1 ≠ 0 := zpow_ne_zero _ hY0
  have e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0
      = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m) := by
    rw [e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]
    simp only [map_mul, map_sub]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdet]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)
    exact (map_ne_zero f).2 (mul_ne_zero hcd hbd)
  · set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m)
      + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq
    set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol
    have hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0)
        = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol := by
      rw [hdet, e00, e11, hA, hB, hPol, hq]
      simp only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]
      ring
    have hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
        < n + m := by
      have h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
          ≤ max n m := by
        refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)
        · rw [natDegree_C]; exact Nat.zero_le _
      omega
    have hqd : q.natDegree = n + m := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]
      exact hrest
    have hPol0 : Pol ≠ 0 := by
      intro h0
      have hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m) := sub_eq_zero.1 (hPol ▸ h0)
      have := congrArg natDegree hsq
      rw [natDegree_pow, hqd] at this
      have hle := natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)
      omega
    rw [hkey]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0

/- English proof (translation)
Introduce `K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd`. Establish `hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) * diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i)) = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i)) (c.map (alge …`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]`. Establish `h2' : (2 : RatFunc K) ≠ 0`. Rewrite using `[show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]`.

Conclude with `(_root_.map_ne_zero _).2 h2`. Take `⟨hd, he⟩` from `discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd`. Rewrite using `[hblk, charpoly_fromBlocks_antidiagonal_fin_two]`. Conclude with `separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he`.
-/
theorem UpperTheory.V.AlgebraTools.discSwap :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ), StrictAnti w₁ → StrictAnti w₂ →
      b 0 0 ≠ 0 → c 0 0 ≠ 0 → b.det ≠ 0 → c.det ≠ 0 →
      ((fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
        diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))).charpoly.Separable := by
  intro K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  have hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
      diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
      = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
          (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]
  have h2' : (2 : RatFunc K) ≠ 0 := by
    rw [show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).2 h2
  obtain ⟨hd, he⟩ := discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  rw [hblk, charpoly_fromBlocks_antidiagonal_fin_two]
  exact separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he
