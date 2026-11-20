import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `M _`. Conclude with `⟨1, fun _ => 0, by simp, fun i => i.elim0, fun i => i.elim0⟩`.

Consider the case `succ m ih`. Introduce `M hM`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, M 0 q ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hM (Matrix.det_eq_zero_of_row_eq_zero 0 h)`. Set `E : Matrix (Fin (m+1)) (Fin (m+1)) K` to `Matrix.of fun i k => Fin.cases (motive := fun _ => K) (if k = 0 then (M 0 q)⁻¹ else 0) (fun (i' : Fin m) => if k = 0 then -(M i'.succ q * (M 0 q)⁻¹) else if k = i'.succ then 1 else 0) i`. Establish `hE0 : ∀ j : Fin (m+1), (E * M) 0 j = (M 0 q)⁻¹ * M 0 j`. Introduce `j`. Simplify using `[E, Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ_ne_zero]`.

Establish `hEs : ∀ (i' : Fin m) (j : Fin (m+1)), (E * M) i'.succ j = M i'.succ j - M i'.succ q * (M 0 q)⁻¹ * M 0 j`. Introduce `i' j`. Simplify using `[E, Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ_ne_zero, Fin.succ_inj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAq0 : (E * M) 0 q = 1` using `by rw [hE0]; exact inv_mul_cancel₀ hq`.

Establish `hAqs : ∀ i' : Fin m, (E * M) i'.succ q = 0`. Introduce `i'`. Rewrite using `[hEs, mul_assoc, inv_mul_cancel₀ hq, mul_one, sub_self]`. Establish `hEtri : E.transpose.BlockTriangular id`. Introduce `i j hij`.

Simplify using `only [transpose_apply]`. Establish `hi : i ≠ 0` using `(lt_of_le_of_lt (Fin.zero_le j) hij).ne'`. Break down `Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩` into its components or cases. Simplify using `[E, hi]`. Simplify using `[E, hi, (show i ≠ j'.succ from hij.ne')]`.

Establish `hdetE : E.det = (M 0 q)⁻¹`. Rewrite using `[← Matrix.det_transpose, Matrix.det_of_upperTriangular hEtri, Fin.prod_univ_succ]`. Simplify using `[E, Fin.succ_ne_zero]`. Establish `hdetA : (E * M).det ≠ 0`. Rewrite using `[Matrix.det_mul, hdetE]`.

Conclude with `mul_ne_zero (inv_ne_zero hq) hM`. Set `M' : Matrix (Fin m) (Fin m) K` to `(E * M).submatrix Fin.succ q.succAbove`. Establish `hM' : M'.det ≠ 0`. Introduce `h0`. Apply `hdetA` to reduce the goal to its premises.

Rewrite using `[Matrix.det_succ_column (E * M) q, Fin.sum_univ_succ]`. Simplify using `only [hAqs, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero]`. Express the relevant statement in the definitionally equal form `_ * _ * M'.det = 0`. Rewrite using `[h0, mul_zero]`. Take `⟨g', s', hg'det, hg'tri, hg'⟩` from `ih M' hM'`.

Set `B : Matrix (Fin (m+1)) (Fin (m+1)) K` to `Matrix.of fun i k => Fin.cases (motive := fun _ => K) (Fin.cases (motive := fun _ => K) 1 (fun _ => 0) k) (fun i' => Fin.cases (motive := fun _ => K) 0 (fun k' => g' i' k') k) i`. Establish `hBsub : B.submatrix Fin.succ Fin.succ = g'`. Use extensionality with `i k`. Simplify using `[B]`. Establish `hdetB : B.det = g'.det`.

Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Simplify using `[B, Fin.succAbove_zero, hBsub]`. Establish `hBtri : B.transpose.BlockTriangular id`. Introduce `i j hij`. Simplify using `only [transpose_apply]`.

Break down `Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩` into its components or cases. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩` into its components or cases. Conclude with `absurd hij (lt_irrefl _)`. Simplify using `[B]`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩` into its components or cases.

Conclude with `absurd hij (Fin.not_lt_zero _)`. Establish `h` using `hg'tri (show id j' < id i' from Fin.succ_lt_succ_iff.mp hij)`. Simplify `h` using `[B]`. Establish `hN0 : ∀ j : Fin (m+1), (B * (E * M)) 0 j = (E * M) 0 j`. Introduce `j`.

Simplify using `[B, Matrix.mul_apply, Fin.sum_univ_succ]`. Establish `hNs : ∀ (i' : Fin m) (j : Fin (m+1)), (B * (E * M)) i'.succ j = ∑ k', g' i' k' * (E * M) k'.succ j`. Introduce `i' j`. Simplify using `[B, Matrix.mul_apply, Fin.sum_univ_succ]`. Establish `hch : (m+1).choose 2 = m + m.choose 2`.

Rewrite using `[Nat.choose_succ_succ', Nat.choose_one_right]`. Set `s : Fin ((m+1).choose 2) → K` to `fun k => Fin.append (fun j' => (E * M) 0 (q.succAbove j')) s' (Fin.cast hch k)`. Use `⟨B * E, s, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, hdetB, hdetE]`. Conclude with `mul_ne_zero hg'det (inv_ne_zero hq)`.

Rewrite using `[Matrix.transpose_mul]`. Conclude with `hEtri.mul hBtri`. Introduce `i j`. Rewrite using `[Matrix.mul_assoc]`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩` into its components or cases.

Rewrite using `[hN0]`. Distinguish the cases in `hj : j = q`. Substitute `hj` using the available equality. Conclude with `Or.inr (Or.inl hAq0)`. Take `⟨j', rfl⟩` from `Fin.exists_succAbove_eq hj`.

Conclude with `Or.inr (Or.inr ⟨Fin.cast hch.symm (Fin.castAdd _ j'), by simp [s, Fin.append_left]⟩)`. Distinguish the cases in `hj : j = q`. Substitute `hj` using the available equality. Use `left`. Rewrite using `[hNs]`.

Simplify using `[hAqs]`. Take `⟨j', rfl⟩` from `Fin.exists_succAbove_eq hj`. Establish `hval : (B * (E * M)) i'.succ (q.succAbove j') = (g' * M') i' j'`. Rewrite using `[hNs]`. Simplify using `[M', Matrix.mul_apply]`.

Rewrite using `[hval]`. Break down `hg' i' j' with h | h | ⟨k, hk⟩` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (Or.inl h)`. Conclude with `Or.inr (Or.inr ⟨Fin.cast hch.symm (Fin.natAdd _ k), by simp [s, Fin.append_right, hk]⟩)`.
-/
theorem echelon_lower_triangular_of_det_ne_zero {K : Type} [Field K] : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) K),
    M.det ≠ 0 →
    ∃ (g : Matrix (Fin m) (Fin m) K) (s : Fin (m.choose 2) → K), g.det ≠ 0 ∧
      g.transpose.BlockTriangular id ∧
      ∀ i j, (g * M) i j = 0 ∨ (g * M) i j = 1 ∨ (g * M) i j ∈ Set.range s := by
  intro m
  induction m with
  | zero =>
    intro M _
    exact ⟨1, fun _ => 0, by simp, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro M hM
    obtain ⟨q, hq⟩ : ∃ q, M 0 q ≠ 0 := by
      by_contra h
      push_neg at h
      exact hM (Matrix.det_eq_zero_of_row_eq_zero 0 h)
    let E : Matrix (Fin (m+1)) (Fin (m+1)) K := Matrix.of fun i k =>
      Fin.cases (motive := fun _ => K) (if k = 0 then (M 0 q)⁻¹ else 0)
        (fun (i' : Fin m) => if k = 0 then -(M i'.succ q * (M 0 q)⁻¹) else if k = i'.succ then 1 else 0) i
    have hE0 : ∀ j : Fin (m+1), (E * M) 0 j = (M 0 q)⁻¹ * M 0 j := by
      intro j
      simp [E, Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ_ne_zero]
    have hEs : ∀ (i' : Fin m) (j : Fin (m+1)), (E * M) i'.succ j = M i'.succ j - M i'.succ q * (M 0 q)⁻¹ * M 0 j := by
      intro i' j
      simp [E, Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ_ne_zero, Fin.succ_inj]
      ring
    have hAq0 : (E * M) 0 q = 1 := by rw [hE0]; exact inv_mul_cancel₀ hq
    have hAqs : ∀ i' : Fin m, (E * M) i'.succ q = 0 := by
      intro i'; rw [hEs, mul_assoc, inv_mul_cancel₀ hq, mul_one, sub_self]
    have hEtri : E.transpose.BlockTriangular id := by
      intro i j hij
      simp only [transpose_apply]
      have hi : i ≠ 0 := (lt_of_le_of_lt (Fin.zero_le j) hij).ne'
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp [E, hi]
      · simp [E, hi, (show i ≠ j'.succ from hij.ne')]
    have hdetE : E.det = (M 0 q)⁻¹ := by
      rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hEtri, Fin.prod_univ_succ]
      simp [E, Fin.succ_ne_zero]
    have hdetA : (E * M).det ≠ 0 := by
      rw [Matrix.det_mul, hdetE]; exact mul_ne_zero (inv_ne_zero hq) hM
    let M' : Matrix (Fin m) (Fin m) K := (E * M).submatrix Fin.succ q.succAbove
    have hM' : M'.det ≠ 0 := by
      intro h0
      apply hdetA
      rw [Matrix.det_succ_column (E * M) q, Fin.sum_univ_succ]
      simp only [hAqs, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
      change _ * _ * M'.det = 0
      rw [h0, mul_zero]
    obtain ⟨g', s', hg'det, hg'tri, hg'⟩ := ih M' hM'
    let B : Matrix (Fin (m+1)) (Fin (m+1)) K := Matrix.of fun i k =>
      Fin.cases (motive := fun _ => K) (Fin.cases (motive := fun _ => K) 1 (fun _ => 0) k)
        (fun i' => Fin.cases (motive := fun _ => K) 0 (fun k' => g' i' k') k) i
    have hBsub : B.submatrix Fin.succ Fin.succ = g' := by
      ext i k; simp [B]
    have hdetB : B.det = g'.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      simp [B, Fin.succAbove_zero, hBsub]
    have hBtri : B.transpose.BlockTriangular id := by
      intro i j hij
      simp only [transpose_apply]
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · exact absurd hij (lt_irrefl _)
        · simp [B]
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · exact absurd hij (Fin.not_lt_zero _)
        · have h := hg'tri (show id j' < id i' from Fin.succ_lt_succ_iff.mp hij)
          simpa [B] using h
    have hN0 : ∀ j : Fin (m+1), (B * (E * M)) 0 j = (E * M) 0 j := by
      intro j; simp [B, Matrix.mul_apply, Fin.sum_univ_succ]
    have hNs : ∀ (i' : Fin m) (j : Fin (m+1)), (B * (E * M)) i'.succ j = ∑ k', g' i' k' * (E * M) k'.succ j := by
      intro i' j; simp [B, Matrix.mul_apply, Fin.sum_univ_succ]
    have hch : (m+1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    let s : Fin ((m+1).choose 2) → K := fun k =>
      Fin.append (fun j' => (E * M) 0 (q.succAbove j')) s' (Fin.cast hch k)
    refine ⟨B * E, s, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hdetB, hdetE]; exact mul_ne_zero hg'det (inv_ne_zero hq)
    · rw [Matrix.transpose_mul]; exact hEtri.mul hBtri
    · intro i j
      rw [Matrix.mul_assoc]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [hN0]
        by_cases hj : j = q
        · subst hj; exact Or.inr (Or.inl hAq0)
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
          exact Or.inr (Or.inr ⟨Fin.cast hch.symm (Fin.castAdd _ j'), by simp [s, Fin.append_left]⟩)
      · by_cases hj : j = q
        · subst hj; left; rw [hNs]; simp [hAqs]
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
          have hval : (B * (E * M)) i'.succ (q.succAbove j') = (g' * M') i' j' := by
            rw [hNs]; simp [M', Matrix.mul_apply]
          rw [hval]
          rcases hg' i' j' with h | h | ⟨k, hk⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨Fin.cast hch.symm (Fin.natAdd _ k), by simp [s, Fin.append_right, hk]⟩)

/- English proof (translation)
Introduce `K _ m M hM`. Establish `hdet : M.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero`. Take `⟨g, s, hg, htri, h⟩` from `echelon_lower_triangular_of_det_ne_zero m M hdet`. Conclude with `⟨g, s, (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg), htri, h⟩`.
-/
theorem echelon_lowerTriangular : ∀ {K : Type} [Field K] (m : ℕ) (M : Matrix (Fin m) (Fin m) K),
    IsUnit M → ∃ (g : Matrix (Fin m) (Fin m) K) (s : Fin (m.choose 2) → K), IsUnit g ∧
      g.transpose.BlockTriangular id ∧
      ∀ i j, (g * M) i j = 0 ∨ (g * M) i j = 1 ∨ (g * M) i j ∈ Set.range s := by
  intro K _ m M hM
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero
  obtain ⟨g, s, hg, htri, h⟩ := echelon_lower_triangular_of_det_ne_zero m M hdet
  exact ⟨g, s, (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg), htri, h⟩

end GlobalTheory
