import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M _`. Conclude with `⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩`.

Consider the case `succ n ih`. Introduce `M hM`. Use `set M' : Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc with hM'`. Establish `hM'min : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (M'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det`. Introduce `k hk`.

Use `hM k (hk.trans n.le_succ)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Both sides reduce to the same expression. Take `⟨L', U', hL'0, hL'1, hU't, hU'd, hLU'⟩` from `ih M' hM'min`.

Establish `hL'det : L'.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L' (fun i j hij => hL'0 i j hij)]`. Simplify using `[hL'1]`. Establish `hL'u : IsUnit L'.det` using `by rw [hL'det]; exact isUnit_one`. Establish `hM'u : IsUnit M'.det`.

Use `hM'min n le_rfl` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hU'u : IsUnit U'.det`.

Rewrite `hM'u` using `[hLU', det_mul, hL'det, one_mul]`. Conclude with `hM'u`. Set `v : Fin n → R` to `fun i => M (Fin.castSucc i) (Fin.last n)`. Set `u : Fin n → R` to `fun j => M (Fin.last n) (Fin.castSucc j)`. Set `a : Fin n → R` to `u ᵥ* U'⁻¹`.

Set `b : Fin n → R` to `L'⁻¹ *ᵥ v`. Set `e : R` to `M (Fin.last n) (Fin.last n) - a ⬝ᵥ b`. Set `L : Matrix (Fin (n+1)) (Fin (n+1)) R` to `Matrix.of fun i j => Fin.lastCases (motive := fun _ => R) (Fin.lastCases (motive := fun _ => R) 1 (fun j' => a j') j) (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => L' i' j') j) i`. Set `U : Matrix (Fin (n+1)) (Fin (n+1)) R` to `Matrix.of fun i j => Fin.lastCases (motive := fun _ => R) (Fin.lastCases (motive := fun _ => R) e (fun _ => 0) j) (fun i' => Fin.lastCases (motive := fun _ => R) (b i') (fun j' => U' i' j') j) i`. Establish `ha : a ᵥ* U' = u`.

Simplify using `only [a]`. Rewrite using `[vecMul_vecMul, nonsing_inv_mul _ hU'u, vecMul_one]`. Establish `hb : L' *ᵥ b = v`. Simplify using `only [b]`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hL'u, one_mulVec]`.

Establish `hL0 : ∀ i j : Fin (n+1), i < j → L i j = 0`. Introduce `i j hij`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [L] at *`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)`.

Consider the case `exact hL'0 _ _ hij`. Establish `hL1 : ∀ i, L i i = 1`. Introduce `i`. Apply the tactic sequence `induction i using Fin.lastCases <;> simp [L, hL'1]`. Establish `hUt : U.BlockTriangular id`.

Introduce `i j hij`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [U] at *`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)`. Consider the case `exact hU't hij`.

Establish `hLU : M = L * U`. Use extensionality with `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [L, U, e, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `cast j`. Establish `hj` using `congrFun ha j`.

Simplify using `only [vecMul, dotProduct, u] at hj`. Simplify using `only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, hj]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Establish `hi` using `congrFun hb i`. Simplify using `only [mulVec, dotProduct, v] at hi`. Simplify using `only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, hi]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `cast j`. Establish `hij` using `congrFun (congrFun hLU' i) j`. Simplify using `only [M', Matrix.submatrix_apply, Matrix.mul_apply] at hij`. Simplify using `only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, hij]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdetL : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L (fun i j hij => hL0 i j hij)]`. Simplify using `[hL1]`. Establish `hMu : IsUnit M.det`. Use `hM (n+1) le_rfl` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `he : IsUnit e`. Rewrite `hMu` using `[hLU, det_mul, hdetL, one_mul, Matrix.det_of_upperTriangular hUt, Fin.prod_univ_castSucc]`.

Use `isUnit_of_mul_isUnit_right hMu` as an intermediate fact. Simplify `this` using `[U]`. Use `⟨L, U, hL0, hL1, hUt, ?_, hLU⟩` and prove the remaining obligations. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => simpa [U] using he`. Consider the case `cast i => simpa [U] using hU'd i`.
-/
theorem lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors :
    ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
        U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  intro R _ n
  induction n with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M hM
    set M' : Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc with hM'
    have hM'min : ∀ (k : ℕ) (hk : k ≤ n),
        IsUnit (M'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have := hM k (hk.trans n.le_succ)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL'0, hL'1, hU't, hU'd, hLU'⟩ := ih M' hM'min
    have hL'det : L'.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L' (fun i j hij => hL'0 i j hij)]
      simp [hL'1]
    have hL'u : IsUnit L'.det := by rw [hL'det]; exact isUnit_one
    have hM'u : IsUnit M'.det := by
      have := hM'min n le_rfl
      convert this using 2
      ext i j; rfl
    have hU'u : IsUnit U'.det := by
      rw [hLU', det_mul, hL'det, one_mul] at hM'u; exact hM'u
    let v : Fin n → R := fun i => M (Fin.castSucc i) (Fin.last n)
    let u : Fin n → R := fun j => M (Fin.last n) (Fin.castSucc j)
    let a : Fin n → R := u ᵥ* U'⁻¹
    let b : Fin n → R := L'⁻¹ *ᵥ v
    let e : R := M (Fin.last n) (Fin.last n) - a ⬝ᵥ b
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 (fun j' => a j') j)
        (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => L' i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) e (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => R) (b i') (fun j' => U' i' j') j) i
    have ha : a ᵥ* U' = u := by
      simp only [a]; rw [vecMul_vecMul, nonsing_inv_mul _ hU'u, vecMul_one]
    have hb : L' *ᵥ b = v := by
      simp only [b]; rw [mulVec_mulVec, mul_nonsing_inv _ hL'u, one_mulVec]
    have hL0 : ∀ i j : Fin (n+1), i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [L] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hL'0 _ _ hij
    have hL1 : ∀ i, L i i = 1 := by
      intro i
      induction i using Fin.lastCases <;> simp [L, hL'1]
    have hUt : U.BlockTriangular id := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [U] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hU't hij
    have hLU : M = L * U := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, e, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, dotProduct]
          ring
        | cast j =>
          have hj := congrFun ha j
          simp only [vecMul, dotProduct, u] at hj
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hj]
          ring
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          have hi := congrFun hb i
          simp only [mulVec, dotProduct, v] at hi
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hi]
          ring
        | cast j =>
          have hij := congrFun (congrFun hLU' i) j
          simp only [M', Matrix.submatrix_apply, Matrix.mul_apply] at hij
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hij]
          ring
    have hdetL : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L (fun i j hij => hL0 i j hij)]
      simp [hL1]
    have hMu : IsUnit M.det := by
      have := hM (n+1) le_rfl
      convert this using 2
      ext i j; rfl
    have he : IsUnit e := by
      rw [hLU, det_mul, hdetL, one_mul, Matrix.det_of_upperTriangular hUt,
        Fin.prod_univ_castSucc] at hMu
      have := isUnit_of_mul_isUnit_right hMu
      simpa [U] using this
    refine ⟨L, U, hL0, hL1, hUt, ?_, hLU⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa [U] using he
    | cast i => simpa [U] using hU'd i
