import Formalism.HermitianCurvature.StatementG

open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset

namespace Formalism.FourierDecayAlt.P.StandardCharacterExists

/- English proof (translation)
Establish `h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i` using `fun i => finSumFinEquiv_symm_apply_castAdd (n := 1) i`. Simplify using `[blk, h]`.
-/
theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

/- English proof (translation)
Establish `h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i` using `fun i => finSumFinEquiv_symm_apply_castAdd (n := 1) i`. Establish `h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1)` using `finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)`. Simplify using `[blk, h, h2]`.
-/
theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

/- English proof (translation)
Establish `h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i` using `fun i => finSumFinEquiv_symm_apply_castAdd (n := 1) i`. Establish `h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1)` using `finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)`. Simplify using `[blk, h, h2]`.
-/
theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

/- English proof (translation)
Establish `h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1)` using `finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)`. Simplify using `[blk, h2]`.
-/
theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h2]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, wMat]`.
-/
theorem wMat_mul_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (wMat d * M) i j = M i.rev j := by
  simp [Matrix.mul_apply, wMat]

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, wMat]`.
-/
theorem wMat_mulVec_apply {d : ℕ} (b : Fin d → ℂ) (i : Fin d) : (wMat d *ᵥ b) i = b i.rev := by
  simp [Matrix.mulVec, dotProduct, wMat]

/- English proof (translation)
Rewrite using `[wMat_mul_apply, Fin.rev_succ, Mcoord]`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]`. Rewrite using `[blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]`. Simplify using the standard rewrite rules.
-/
theorem wM_succ {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n)
    (j : Fin (n + 1)) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) i.succ j = blk X B 0 0 i.castSucc j := by
  rw [wMat_mul_apply, Fin.rev_succ, Mcoord]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
  · rw [blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]; simp

/- English proof (translation)
Rewrite using `[wMat_mul_apply, Fin.rev_zero, Mcoord, blk_lc]`.
-/
theorem wM_zero_cast {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (j : Fin n) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) 0 j.castSucc = ρ j := by
  rw [wMat_mul_apply, Fin.rev_zero, Mcoord, blk_lc]

/- English proof (translation)
Rewrite using `[wMat_mul_apply, Fin.rev_zero, Mcoord, blk_ll]`.
-/
theorem wM_zero_last {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) 0 (Fin.last n) = σ := by
  rw [wMat_mul_apply, Fin.rev_zero, Mcoord, blk_ll]

/- English proof (translation)
Introduce `i j hji`. Use `Fin.lastCases ?_ (fun i => ?_) i hji` and prove the remaining obligations. Introduce `_`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[blk_ll]`.

Rewrite using `[blk_lc]`. Both sides reduce to the same expression. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Introduce `h`. Conclude with `absurd h (not_le.mpr (Fin.castSucc_lt_last i))`.

Introduce `h`. Rewrite using `[blk_cc]`. Conclude with `hX i j (by simpa using h)`.
-/
theorem blk_strictUpper {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (hX : IsStrictUpper X) :
    IsStrictUpper (blk X B 0 0) := by
  intro i j hji
  refine Fin.lastCases ?_ (fun i => ?_) i hji
  · intro _
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [blk_ll]
    · rw [blk_lc]; rfl
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      exact absurd h (not_le.mpr (Fin.castSucc_lt_last i))
    · intro h
      rw [blk_cc]
      exact hX i j (by simpa using h)

def ex {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : ℕ) : ℂ :=
  if h : a < d ∧ b < d then N ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/- English proof (translation)
Simplify using `[ex]`.
-/
theorem ex_fin {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) : ex N i j = N i j := by
  simp [ex]

/- English proof (translation)
Use `ex_fin (blk X B 0 0) i.castSucc k.castSucc` as an intermediate fact. Rewrite `this` using `[blk_cc]`. Simplify using `using this.symm`.
-/
theorem X_eq_ex {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (i k : Fin n) :
    X i k = ex (blk X B 0 0) i k := by
  have := ex_fin (blk X B 0 0) i.castSucc k.castSucc
  rw [blk_cc] at this
  simpa using this.symm

/- English proof (translation)
Use `ex_fin (blk X B 0 0) i.castSucc (Fin.last n)` as an intermediate fact. Rewrite `this` using `[blk_cl]`. Simplify using `using this.symm`.
-/
theorem B_eq_ex {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (i : Fin n) :
    B i = ex (blk X B 0 0) i n := by
  have := ex_fin (blk X B 0 0) i.castSucc (Fin.last n)
  rw [blk_cl] at this
  simpa using this.symm

/- English proof (translation)
Use `ex_fin (blk X B 0 0) k.castSucc k.succ` as an intermediate fact. Simplify `this.symm` using `[xOf]`.
-/
theorem x_eq_ex {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (k : Fin n) :
    xOf X B k = ex (blk X B 0 0) k (k + 1) := by
  have := ex_fin (blk X B 0 0) k.castSucc k.succ
  simpa [xOf] using this.symm

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Use `⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h` using `hx i`. Rewrite `h` using `[x_eq_ex]`. Simplify using `only [pow_zero, Matrix.one_mulVec, one_mul]`. Rewrite using `[B_eq_ex X B i, ← h]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [pow_zero, Matrix.one_mulVec, one_mul]`. Establish `hI : Finset.Ico (i : ℕ) m = {(i : ℕ)}`. Use extensionality with `a`. Simplify using `only [Finset.mem_Ico, Finset.mem_singleton]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hI, Finset.sum_singleton, B_eq_ex X B i]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`.

Take `⟨ih0, ih1, ih2⟩` from `ih`. Establish `hstep : ∀ i : Fin (m + 1), ((-X) ^ (j + 1) *ᵥ B) i = ∑ k, -(X i k * ((-X) ^ j *ᵥ B) k)`. Introduce `i`. Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec, dotProduct]`.

Use `⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[hstep]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ≤ i`. Rewrite using `[hX i k hk]`.

Simplify using the standard rewrite rules. Establish `hk' : (i : ℕ) < k` using `by simpa using hk`. Rewrite using `[ih0 k (by omega)]; simp`. Rewrite using `[hstep]`. Establish `hlt : (i : ℕ) + 1 < m + 1` using `by omega`.

Rewrite using `[Finset.sum_eq_single (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1))]`. Rewrite using `[ih1 _ (by simp only; omega)]`. Establish `h` using `hx i`. Rewrite `h` using `[x_eq_ex]`. Rewrite using `[X_eq_ex X B]`.

Simplify using `only`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `k _ hk`. Distinguish the cases in `hk1 : k ≤ i`.

Rewrite using `[hX i k hk1]`. Simplify using the standard rewrite rules. Establish `hk' : (i : ℕ) < k` using `by simpa using hk1`. Establish `hk2 : (k : ℕ) ≠ (i : ℕ) + 1` using `fun h => hk (Fin.ext h)`. Rewrite using `[ih0 k (by omega)]; simp`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hstep]`. Establish `hlt : (i : ℕ) + 1 < m + 1` using `by omega`. Establish `hlt2 : (i : ℕ) + 2 < m + 1` using `by omega`.

Rewrite using `[Finset.sum_eq_add (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1)) (⟨(i : ℕ) + 2, hlt2⟩ : Fin (m + 1))]`. Rewrite using `[ih2 _ (by simp only; omega), ih1 _ (by simp only; omega)]`. Establish `h` using `hx i`. Rewrite `h` using `[x_eq_ex]`. Rewrite using `[X_eq_ex X B, X_eq_ex X B]`.

Simplify using `only`. Rewrite using `[h, Finset.sum_eq_sum_Ico_succ_bot (show (i : ℕ) < m by omega)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Introduce `k _ hk`. Distinguish the cases in `hk1 : k ≤ i`. Rewrite using `[hX i k hk1]`. Simplify using the standard rewrite rules.

Establish `hk' : (i : ℕ) < k` using `by simpa using hk1`. Establish `hk2 : (k : ℕ) ≠ (i : ℕ) + 1` using `fun h => hk.1 (Fin.ext h)`. Establish `hk3 : (k : ℕ) ≠ (i : ℕ) + 2` using `fun h => hk.2 (Fin.ext h)`. Rewrite using `[ih0 k (by omega)]; simp`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem key (m : ℕ) (z : ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (hX : IsStrictUpper X) (hx : ∀ k, xOf X B k = z) (j : ℕ) :
    (∀ i : Fin (m + 1), m < (i : ℕ) + j → ((-X) ^ j *ᵥ B) i = 0) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j = m → ((-X) ^ j *ᵥ B) i = (-z) ^ j * z) ∧
    (∀ i : Fin (m + 1), (i : ℕ) + j + 1 = m →
      ((-X) ^ j *ᵥ B) i = (-z) ^ j * ∑ k ∈ Finset.Ico (i : ℕ) m, ex (blk X B 0 0) k (k + 2)) := by
  induction j with
  | zero =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · have := i.isLt; omega
    · have h := hx i
      rw [x_eq_ex] at h
      simp only [pow_zero, Matrix.one_mulVec, one_mul]
      rw [B_eq_ex X B i, ← h]
      congr 1; omega
    · simp only [pow_zero, Matrix.one_mulVec, one_mul]
      have hI : Finset.Ico (i : ℕ) m = {(i : ℕ)} := by
        ext a; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [hI, Finset.sum_singleton, B_eq_ex X B i]
      congr 1; omega
  | succ j ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have hstep : ∀ i : Fin (m + 1), ((-X) ^ (j + 1) *ᵥ B) i = ∑ k, -(X i k * ((-X) ^ j *ᵥ B) k) := by
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hstep]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k ≤ i
      · rw [hX i k hk]; simp
      · have hk' : (i : ℕ) < k := by simpa using hk
        rw [ih0 k (by omega)]; simp
    · rw [hstep]
      have hlt : (i : ℕ) + 1 < m + 1 := by omega
      rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1))]
      · rw [ih1 _ (by simp only; omega)]
        have h := hx i
        rw [x_eq_ex] at h
        rw [X_eq_ex X B]
        simp only
        rw [h]; ring
      · intro k _ hk
        by_cases hk1 : k ≤ i
        · rw [hX i k hk1]; simp
        · have hk' : (i : ℕ) < k := by simpa using hk1
          have hk2 : (k : ℕ) ≠ (i : ℕ) + 1 := fun h => hk (Fin.ext h)
          rw [ih0 k (by omega)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [hstep]
      have hlt : (i : ℕ) + 1 < m + 1 := by omega
      have hlt2 : (i : ℕ) + 2 < m + 1 := by omega
      rw [Finset.sum_eq_add (⟨(i : ℕ) + 1, hlt⟩ : Fin (m + 1)) (⟨(i : ℕ) + 2, hlt2⟩ : Fin (m + 1))]
      · rw [ih2 _ (by simp only; omega), ih1 _ (by simp only; omega)]
        have h := hx i
        rw [x_eq_ex] at h
        rw [X_eq_ex X B, X_eq_ex X B]
        simp only
        rw [h, Finset.sum_eq_sum_Ico_succ_bot (show (i : ℕ) < m by omega)]
        ring
      · intro h
        have := congrArg Fin.val h
        simp at this
      · intro k _ hk
        by_cases hk1 : k ≤ i
        · rw [hX i k hk1]; simp
        · have hk' : (i : ℕ) < k := by simpa using hk1
          have hk2 : (k : ℕ) ≠ (i : ℕ) + 1 := fun h => hk.1 (Fin.ext h)
          have hk3 : (k : ℕ) ≠ (i : ℕ) + 2 := fun h => hk.2 (Fin.ext h)
          rw [ih0 k (by omega)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single m]`. Simplify using the standard rewrite rules. Introduce `j hj hne`. Establish `: j < m + 1` using `Finset.mem_range.mp hj`. Rewrite using `[zero_pow (by omega), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h`.
-/
theorem poly_zero (m : ℕ) (c : ℕ → ℂ) : ∑ j ∈ Finset.range (m + 1), c j * (0 : ℂ) ^ (m - j) = c m := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hne
    have : j < m + 1 := Finset.mem_range.mp hj
    rw [zero_pow (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

/- English proof (translation)
Simplify using `using hasDerivAt_const (0 : ℂ) (c 0)`.
-/
theorem poly_deriv_zero (c : ℕ → ℂ) :
    HasDerivAt (fun t : ℂ => ∑ j ∈ Finset.range (0 + 1), c j * t ^ (0 - j)) 0 0 := by
  simpa using hasDerivAt_const (0 : ℂ) (c 0)

/- English proof (translation)
Establish `h : ∀ j ∈ Finset.range (m + 1 + 1), HasDerivAt (fun t : ℂ => c j * t ^ (m + 1 - j)) (c j * (((m + 1 - j : ℕ) : ℂ) * (0 : ℂ) ^ (m + 1 - j - 1))) 0` using `fun j _ => (hasDerivAt_pow (m + 1 - j) (0 : ℂ)).const_mul (c j)`. Establish `h2` using `HasDerivAt.fun_sum h`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single m]`. Simplify using the standard rewrite rules.

Introduce `j hj hne`. Establish `: j < m + 1 + 1` using `Finset.mem_range.mp hj`. Distinguish the cases in `hj' : j = m + 1`. Substitute `hj'` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[zero_pow (by omega)]; simp`. Introduce `h; exact absurd (Finset.mem_range.mpr (by omega)) h`.
-/
theorem poly_deriv_succ (m : ℕ) (c : ℕ → ℂ) :
    HasDerivAt (fun t : ℂ => ∑ j ∈ Finset.range (m + 1 + 1), c j * t ^ (m + 1 - j)) (c m) 0 := by
  have h : ∀ j ∈ Finset.range (m + 1 + 1), HasDerivAt (fun t : ℂ => c j * t ^ (m + 1 - j))
      (c j * (((m + 1 - j : ℕ) : ℂ) * (0 : ℂ) ^ (m + 1 - j - 1))) 0 := fun j _ =>
    (hasDerivAt_pow (m + 1 - j) (0 : ℂ)).const_mul (c j)
  have h2 := HasDerivAt.fun_sum h
  refine h2.congr_deriv ?_
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hne
    have : j < m + 1 + 1 := Finset.mem_range.mp hj
    by_cases hj' : j = m + 1
    · subst hj'; simp
    · rw [zero_pow (by omega)]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/- English proof (translation)
Establish `hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2`. Establish `h1` using `Algebra.norm_complex_apply α`. Rewrite `h1` using `[Algebra.norm_apply]`. Rewrite using `[← Complex.normSq_eq_norm_sq, ← h1]`. Both sides reduce to the same expression.

Establish `h` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)`. Rewrite `h` using `[hdet, abs_of_nonneg (by positivity)]`. Conclude with `h`.
-/
theorem map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2 := by
    have h1 := Algebra.norm_complex_apply α
    rw [Algebra.norm_apply] at h1
    rw [← Complex.normSq_eq_norm_sq, ← h1]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

/- English proof (translation)
Unfold `mu`. Rewrite using `[Measure.map_smul, map_mul_vol α hα]`. Rewrite using `[smul_comm]`. Use `congr 1`.
-/
theorem map_mul_mu (β α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (mu β) = Real.toNNReal ((‖α‖ ^ 2)⁻¹) • mu β := by
  unfold mu
  rw [Measure.map_smul, map_mul_vol α hα]
  rw [smul_comm]
  congr 1

/- English proof (translation)
Unfold `muPi`. Establish `hA` using `map_mul_mu β z hz`. Establish `hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i`. Use extensionality with `v i`. Simplify using the standard rewrite rules.

Establish `hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) = (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι`. Rewrite using `[← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]`. Establish `hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β))`. Rewrite using `[hA]`. Use `infer_instance`.

Rewrite using `[hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]`. Simplify using `only [hA]`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[hc]`. Simplify using `only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]`.
-/
theorem scalePi (β z : ℂ) (ι : Type) [Fintype ι] (hz : z ≠ 0) :
    Measure.map (fun v : ι → ℂ => z • v) (muPi β ι) =
      Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • muPi β ι := by
  unfold muPi
  have hA := map_mul_mu β z hz
  have hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i := by
    ext v i; simp
  have hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) =
      (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι := by
    rw [← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]
  have hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β)) := by
    rw [hA]; infer_instance
  rw [hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]
  simp only [hA]
  refine Measure.pi_eq fun s hs => ?_
  rw [hc]
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]`. Repeatedly rewrite using `[← Finset.card_filter]`. Establish `: ∀ y : Fin n, (univ.filter (fun x : Fin n => x < y)).card = (y : ℕ)`. Introduce `y`. Rewrite using `[show univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]`.

Conclude with `Fin.card_Iio y`. Repeatedly rewrite using `[this]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => i) n`.
-/
theorem card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ range n, i := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp_rw [← Finset.card_filter]
  have : ∀ y : Fin n, (univ.filter (fun x : Fin n => x < y)).card = (y : ℕ) := by
    intro y
    rw [show univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]
    exact Fin.card_Iio y
  simp_rw [this]
  exact Fin.sum_univ_eq_sum_range (fun i => i) n

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i < j <;> simp [strictUpper, h]`.
-/
theorem strictUpper_smul {d : ℕ} (a : ℂ) (y : UT d → ℂ) : strictUpper (a • y) = a • strictUpper y := by
  ext i j
  by_cases h : i < j <;> simp [strictUpper, h]

/- English proof (translation)
Unfold `superSum`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: i.castSucc ≠ i.succ` using `(Fin.castSucc_lt_succ (i := i)).ne`. Simplify using `[this]`.
-/
theorem superSum_one_add {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    superSum (1 + S) = superSum S := by
  unfold superSum
  refine Finset.sum_congr rfl fun i _ => ?_
  have : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  simp [this]

/- English proof (translation)
Unfold `superSum`. Rewrite using `[Fin.sum_univ_succ]`. Use `congr 1`. Use `wM_zero_cast X B ρ σ 1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[← Finset.range_eq_Ico, Finset.sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Fin.succ_castSucc, wM_succ]`. Simplify using `using (ex_fin (blk X B 0 0) i.castSucc.castSucc i.succ.succ).symm`.
-/
theorem superSum_wM (m : ℕ) (X : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (B ρ : Fin (m + 2) → ℂ) (σ : ℂ) :
    superSum (wMat (m + 3) * Mcoord 0 X B ρ σ) =
      ρ 1 + ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) := by
  unfold superSum
  rw [Fin.sum_univ_succ]
  congr 1
  · have := wM_zero_cast X B ρ σ 1
    simpa using this
  · rw [← Finset.range_eq_Ico, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.succ_castSucc, wM_succ]
    simpa using (ex_fin (blk X B 0 0) i.castSucc.castSucc i.succ.succ).symm

end Formalism.FourierDecayAlt.P.StandardCharacterExists

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.StandardCharacterExists

/- English proof (translation)
Introduce `m z σ ρ' X B hX hx i j hji`. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Use `Fin.cases ?_ (fun i => ?_) i hji` and prove the remaining obligations. Introduce `h`. Establish `hj : j = 0` using `le_antisymm h (Fin.zero_le _)`.

Substitute `hj` using the available equality. Use `wM_zero_cast X B (Fin.cons z ρ') σ 0` as an intermediate fact. Simplify using `only [Fin.castSucc_zero, Fin.cons_zero] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Introduce `h`. Rewrite using `[wM_succ]`. Break down `h.eq_or_lt with h | h` into its components or cases. Substitute `h` using the available equality. Use `hx i` as an intermediate fact.

Unfold `xOf at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[blk_strictUpper X B hX _ _ (Fin.le_castSucc_iff.mpr h), Matrix.one_apply_ne h.ne']`. Simplify using the standard rewrite rules.
-/
theorem limit_shape : Formalism.FourierDecayAlt.G.LimitShape := by
  intro m z σ ρ' X B hX hx i j hji
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) i hji
  · intro h
    have hj : j = 0 := le_antisymm h (Fin.zero_le _)
    subst hj
    have := wM_zero_cast X B (Fin.cons z ρ') σ 0
    simp only [Fin.castSucc_zero, Fin.cons_zero] at this
    rw [this]; simp
  · intro h
    rw [wM_succ]
    rcases h.eq_or_lt with h | h
    · subst h
      have := hx i
      unfold xOf at this
      rw [this]; simp
    · rw [blk_strictUpper X B hX _ _ (Fin.le_castSucc_iff.mpr h), Matrix.one_apply_ne h.ne']
      simp

/- English proof (translation)
Introduce `n z hz y`. Prove the components needed by the constructor for the conclusion. Rewrite using `[ptLong, upper, strictUpper_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]`. Rewrite using `[upper, superSum_one_add, strictUpper_smul]`. Simplify using `[superSum, Finset.mul_sum, div_eq_inv_mul]`.
-/
theorem limit_matrix : Formalism.FourierDecayAlt.G.LimitMatrix := by
  intro n z hz y
  constructor
  · rw [ptLong, upper, strictUpper_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
  · rw [upper, superSum_one_add, strictUpper_smul]
    simp [superSum, Finset.mul_sum, div_eq_inv_mul]

/- English proof (translation)
Introduce `n β z hz V _ _ _ Φ`. Use `set μ := muPi β (UT (n + 1)) with hμ`. Use `set F : (UT (n + 1) → ℂ) → V := fun y => psi β (superSum (strictUpper y) / z) • Φ (wMat (n + 1) * (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + strictUpper y)) with hF`. Establish `hS` using `scalePi β z (UT (n + 1)) hz`. Establish `hemb : MeasurableEmbedding (fun v : UT (n + 1) → ℂ => z • v)` using `measurableEmbedding_const_smul₀ hz`.

Establish `h1 : ∫ y, F y ∂(Measure.map (fun v : UT (n + 1) → ℂ => z • v) μ) = ∫ v, F (z • v) ∂μ` using `hemb.integral_map F`. Establish `h2 : ∀ v : UT (n + 1) → ℂ, F (z • v) = psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v)`. Introduce `v`. Take `⟨e1, e2⟩` from `limit_matrix n z hz (z • v)`. Rewrite `e1`, `e2` using `[smul_smul, inv_mul_cancel₀ hz, one_smul]`.

Simplify using `only [hF]`. Rewrite using `[e1, e2]`. Rewrite `h1` using `[hS, integral_smul_nnreal_measure]`. Simplify using `only [h2] at h1`. Establish `hcard : 2 * Fintype.card (UT (n + 1)) = (n + 1) * n`.

Rewrite using `[card_UT, mul_comm]`. Simplify using `using Finset.sum_range_id_mul_two (n + 1)`. Rewrite `h1` using `[hcard]`. Unfold `OmLong`. Rewrite using `[← h1]`.

Establish `hpos : (0 : ℝ) < ‖z‖ ^ ((n + 1) * n)` using `by positivity`. Rewrite using `[NNReal.smul_def, Real.coe_toNNReal _ (by positivity), ← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]`.
-/
theorem limit_integral : Formalism.FourierDecayAlt.G.LimitIntegral := by
  intro n β z hz V _ _ _ Φ
  set μ := muPi β (UT (n + 1)) with hμ
  set F : (UT (n + 1) → ℂ) → V := fun y => psi β (superSum (strictUpper y) / z) •
          Φ (wMat (n + 1) * (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + strictUpper y)) with hF
  have hS := scalePi β z (UT (n + 1)) hz
  have hemb : MeasurableEmbedding (fun v : UT (n + 1) → ℂ => z • v) := measurableEmbedding_const_smul₀ hz
  have h1 : ∫ y, F y ∂(Measure.map (fun v : UT (n + 1) → ℂ => z • v) μ) = ∫ v, F (z • v) ∂μ :=
    hemb.integral_map F
  have h2 : ∀ v : UT (n + 1) → ℂ, F (z • v) =
      psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v) := by
    intro v
    obtain ⟨e1, e2⟩ := limit_matrix n z hz (z • v)
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at e1 e2
    simp only [hF]
    rw [e1, e2]
  rw [hS, integral_smul_nnreal_measure] at h1
  simp only [h2] at h1
  have hcard : 2 * Fintype.card (UT (n + 1)) = (n + 1) * n := by
    rw [card_UT, mul_comm]
    simpa using Finset.sum_range_id_mul_two (n + 1)
  rw [hcard] at h1
  unfold OmLong
  rw [← h1]
  have hpos : (0 : ℝ) < ‖z‖ ^ ((n + 1) * n) := by positivity
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), ← Complex.coe_smul, smul_smul,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

/- English proof (translation)
Introduce `m z D σ ρ' X B hz hD hX hx`. Establish `hD' : D = -((-z) ^ m * z * z)`. Establish `h1 : ((-1 : ℂ) ^ (m + 3)) * ((-1 : ℂ) ^ (m + 3)) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Establish `hCne : (-z) ^ m * z ≠ 0` using `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hz)) hz`. Take `⟨k0, k1, -⟩` from `key m z X B hX hx m`. Establish `hC0 : Cof X B 0 = (-z) ^ m * z`. Unfold `Cof`.

Rewrite using `[poly_zero m (fun j => ((-X) ^ j *ᵥ B) 0)]`. Conclude with `k1 0 (by simp)`. Establish `hR0 : R0 X B ρ' 0 = 0`. Unfold `R0`. Rewrite using `[poly_zero m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[k0 k.succ (by simp), mul_zero]`. Establish `hval : rho1 D σ ρ' X B 0 = z`. Unfold `rho1`. Rewrite using `[hC0, hR0, hD', zero_pow (by omega)]`.

Simplify using `only [zero_mul, zero_sub, neg_neg, sub_zero]`. Conclude with `mul_div_cancel_left₀ z hCne`. Use `⟨hval, ?_⟩` and prove the remaining obligations. Establish `hnum0 : (0 : ℂ) ^ (m + 1) * σ - D - R0 X B ρ' 0 = (-z) ^ m * z * z`. Rewrite using `[hR0, hD', zero_pow (by omega)]; ring`.

Establish `hCne' : Cof X B 0 ≠ 0` using `by rw [hC0]; exact hCne`. Consider the cases of `m with`. Consider the case `zero`. Establish `hNum : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D - R0 X B ρ' t) (1 * σ - 0) 0`. Establish `h1 : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D) (1 * σ) 0`.

Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const σ).sub_const D`. Conclude with `h1.sub (poly_deriv_zero (fun j => ∑ k : Fin 0, ρ' k * ((-X) ^ j *ᵥ B) k.succ))`. Establish `hCof : HasDerivAt (fun t : ℂ => Cof X B t) 0 0` using `poly_deriv_zero (fun j => ((-X) ^ j *ᵥ B) 0)`. Establish `hdiv` using `hNum.div hCof hCne'`. Use `hdiv.congr_deriv ?_` and prove the remaining obligations.

Establish `hs : superSum (wMat (0 + 2) * Mcoord 0 X B (Fin.cons z ρ') σ) = σ`. Unfold `superSum`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `using wM_zero_last X B (Fin.cons z ρ') σ`. Rewrite using `[hs, hC0]`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Consider the case `succ m`. Take `⟨l0, l1, l2⟩` from `key (m + 1) z X B hX hx m`. Establish `hNum : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D - R0 X B ρ' t) (0 - ρ' 0 * ((-z) ^ m * z)) 0`.

Establish `h1 : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D) 0 0`. Simplify using `using ((hasDerivAt_pow (m + 1 + 1) (0 : ℂ)).mul_const σ).sub_const D`. Establish `h2` using `poly_deriv_succ m (fun j => ∑ k : Fin (m + 1), ρ' k * ((-X) ^ j *ᵥ B) k.succ)`. Establish `h3 : ∑ k : Fin (m + 1), ρ' k * ((-X) ^ m *ᵥ B) k.succ = ρ' 0 * ((-z) ^ m * z)`. Rewrite using `[Fin.sum_univ_succ, l1 (Fin.succ 0) (by simp; omega)]`.

Rewrite using `[Finset.sum_eq_zero, add_zero]`. Introduce `k _`. Rewrite using `[l0 k.succ.succ (by simp; omega), mul_zero]`. Rewrite `h2` using `[h3]`. Conclude with `h1.sub h2`.

Establish `hCof : HasDerivAt (fun t : ℂ => Cof X B t) ((-z) ^ m * ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2)) 0`. Establish `h2` using `poly_deriv_succ m (fun j => ((-X) ^ j *ᵥ B) 0)`. Rewrite `h2` using `[l2 0 (by simp)]`. Conclude with `h2`. Establish `hdiv` using `hNum.div hCof hCne'`.

Use `hdiv.congr_deriv ?_` and prove the remaining obligations. Establish `hc1 : (Fin.cons z ρ' : Fin (m + 2) → ℂ) 1 = ρ' 0` using `Fin.cons_succ (α := fun _ => ℂ) z ρ' 0`. Rewrite using `[superSum_wM, hc1, hnum0, hC0]`. Establish `ha : (-z) ^ m ≠ 0` using `pow_ne_zero _ (neg_ne_zero.mpr hz)`. Rewrite using `[pow_succ]`.

Generalize the expression as in `(-z) ^ m = a at ha`. Generalize the expression as in `∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) = T`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reduced_phase_critical_points : Formalism.FourierDecayAlt.G.CornerEntryCritical := by
  intro m z D σ ρ' X B hz hD hX hx
  have hD' : D = -((-z) ^ m * z * z) := by
    have h1 : ((-1 : ℂ) ^ (m + 3)) * ((-1 : ℂ) ^ (m + 3)) = 1 := by
      rw [← mul_pow]; simp
    calc D = ((-1 : ℂ) ^ (m + 3)) * ((-1 : ℂ) ^ (m + 3) * D) := by rw [← mul_assoc, h1, one_mul]
      _ = ((-1 : ℂ) ^ (m + 3)) * z ^ (m + 2) := by rw [hD]
      _ = -((-z) ^ m * z * z) := by rw [neg_pow z m]; ring
  have hCne : (-z) ^ m * z ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hz)) hz
  obtain ⟨k0, k1, -⟩ := key m z X B hX hx m
  have hC0 : Cof X B 0 = (-z) ^ m * z := by
    unfold Cof
    rw [poly_zero m (fun j => ((-X) ^ j *ᵥ B) 0)]
    exact k1 0 (by simp)
  have hR0 : R0 X B ρ' 0 = 0 := by
    unfold R0
    rw [poly_zero m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [k0 k.succ (by simp), mul_zero]
  have hval : rho1 D σ ρ' X B 0 = z := by
    unfold rho1
    rw [hC0, hR0, hD', zero_pow (by omega)]
    simp only [zero_mul, zero_sub, neg_neg, sub_zero]
    exact mul_div_cancel_left₀ z hCne
  refine ⟨hval, ?_⟩
  have hnum0 : (0 : ℂ) ^ (m + 1) * σ - D - R0 X B ρ' 0 = (-z) ^ m * z * z := by
    rw [hR0, hD', zero_pow (by omega)]; ring
  have hCne' : Cof X B 0 ≠ 0 := by rw [hC0]; exact hCne
  cases m with
  | zero =>
    have hNum : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D - R0 X B ρ' t) (1 * σ - 0) 0 := by
      have h1 : HasDerivAt (fun t : ℂ => t ^ (0 + 1) * σ - D) (1 * σ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const σ).sub_const D
      exact h1.sub (poly_deriv_zero (fun j => ∑ k : Fin 0, ρ' k * ((-X) ^ j *ᵥ B) k.succ))
    have hCof : HasDerivAt (fun t : ℂ => Cof X B t) 0 0 :=
      poly_deriv_zero (fun j => ((-X) ^ j *ᵥ B) 0)
    have hdiv := hNum.div hCof hCne'
    refine hdiv.congr_deriv ?_
    have hs : superSum (wMat (0 + 2) * Mcoord 0 X B (Fin.cons z ρ') σ) = σ := by
      unfold superSum
      rw [Fin.sum_univ_succ]
      simpa using wM_zero_last X B (Fin.cons z ρ') σ
    rw [hs, hC0]
    field_simp
    simp
  | succ m =>
    obtain ⟨l0, l1, l2⟩ := key (m + 1) z X B hX hx m
    have hNum : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D - R0 X B ρ' t)
        (0 - ρ' 0 * ((-z) ^ m * z)) 0 := by
      have h1 : HasDerivAt (fun t : ℂ => t ^ (m + 1 + 1) * σ - D) 0 0 := by
        simpa using ((hasDerivAt_pow (m + 1 + 1) (0 : ℂ)).mul_const σ).sub_const D
      have h2 := poly_deriv_succ m (fun j => ∑ k : Fin (m + 1), ρ' k * ((-X) ^ j *ᵥ B) k.succ)
      have h3 : ∑ k : Fin (m + 1), ρ' k * ((-X) ^ m *ᵥ B) k.succ = ρ' 0 * ((-z) ^ m * z) := by
        rw [Fin.sum_univ_succ, l1 (Fin.succ 0) (by simp; omega)]
        rw [Finset.sum_eq_zero, add_zero]
        intro k _
        rw [l0 k.succ.succ (by simp; omega), mul_zero]
      rw [h3] at h2
      exact h1.sub h2
    have hCof : HasDerivAt (fun t : ℂ => Cof X B t)
        ((-z) ^ m * ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2)) 0 := by
      have h2 := poly_deriv_succ m (fun j => ((-X) ^ j *ᵥ B) 0)
      rw [l2 0 (by simp)] at h2
      exact h2
    have hdiv := hNum.div hCof hCne'
    refine hdiv.congr_deriv ?_
    have hc1 : (Fin.cons z ρ' : Fin (m + 2) → ℂ) 1 = ρ' 0 := Fin.cons_succ (α := fun _ => ℂ) z ρ' 0
    rw [superSum_wM, hc1, hnum0, hC0]
    have ha : (-z) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hz)
    rw [pow_succ]
    generalize (-z) ^ m = a at ha
    generalize ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) = T
    field_simp
    ring

end Formalism.FourierDecayAlt.P
