import Mathlib
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `n r J X hX l d h u A X₁ Xb X₂ h1 hb hperp`. Establish `hext : ∀ (m : ℕ) (hm : m ≤ r) (a : Fin m → ℂ), Matrix.mulVec X (fun i : Fin r => if hi : i.val < m then a ⟨i.val, hi⟩ else 0) = Matrix.mulVec (X.submatrix id fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) a`. Introduce `m hm a`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]`.

Use `symm`. Use `Fintype.sum_of_injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) ?_ _ _ ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Conclude with `Fin.ext (by simpa using congrArg Fin.val hxy)`. Introduce `i hi`.

Establish `: ¬ i.val < m`. Introduce `hlt`. Conclude with `hi ⟨⟨i.val, hlt⟩, rfl⟩`. Simplify using `[this]`. Introduce `j`.

Simplify using the standard rewrite rules. Establish `he1 : ∀ a : Fin l → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0) = Matrix.mulVec X₁ a` using `fun a => hext l (by omega) a`. Establish `he2 : ∀ a : Fin (l + d) → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l + d then a ⟨i.val, hi⟩ else 0) = Matrix.mulVec X₂ a` using `fun a => hext (l + d) h a`. Establish `hcol : ∀ (v : Fin n → ℂ) (i : Fin (l + d)), Matrix.mulVec (X₂.conjTranspose * J) v i = Matrix.mulVec (X.conjTranspose * J) v ⟨i.val, by omega⟩`. Introduce `v i`.

Both sides reduce to the same expression. Establish `hXc : ∀ (i j : Fin r), Matrix.mulVec (X.conjTranspose * J) (fun k => X k j) i = 0`. Introduce `i j`. Conclude with `congrFun (congrFun hX i) j`. Establish `key : ∀ j : Fin r, ∃ c : Fin r → ℂ, (∀ i, c i ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧ Matrix.mulVec u (fun k => X k j) = (fun k => X k j) + Matrix.mulVec X c`.

Introduce `j`. Distinguish the cases in `hj1 : j.val < l`. Use `⟨0, fun i hi => absurd rfl hi, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `congrFun (congrFun h1 k) ⟨j.val, hj1⟩` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, X₁]`. Distinguish the cases in `hj2 : j.val < l + d`. Use `⟨fun i => if hi : i.val < l then A ⟨i.val, hi⟩ ⟨j.val - l, by omega⟩ else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi left`. Distinguish the cases in `hil : i.val < l`.

Conclude with `⟨hil, by omega⟩`. Conclude with `absurd (by simp [hil]) hi`. Establish `he1'` using `he1 (fun i => A i ⟨j.val - l, by omega⟩) beta_reduce at he1'`. Rewrite using `[he1']`. Use function extensionality and compare the values at `k`.

Use `congrFun (congrFun hb k) ⟨j.val - l, by omega⟩` as an intermediate fact. Establish `hjj : (⟨l + (j.val - l), by omega⟩ : Fin r) = j` using `Fin.ext (by simp; omega)`. Simplify using `only [Matrix.mul_apply, Matrix.add_apply, Xb, X₁, Matrix.submatrix_apply, id, hjj] at this`. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, X₁]`. Establish `hz : Matrix.mulVec (X₂.conjTranspose * J) (fun k => X k j) = 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[hcol]`. Conclude with `hXc _ _`. Take `⟨w, a, hwa⟩` from `hperp _ hz`. Use `⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) + (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi right`. Use `⟨?_, by omega⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hc' : ¬ i.val < l` using `by omega`. Conclude with `hi (by simp [hc, hc'])`.

Rewrite using `[Matrix.mulVec_add, he1, he2, ← hwa]`. Normalize the expressions using the abelian group laws. Use `choose c hc hc' using key`. Use `⟨Matrix.of fun i j => c j i, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `k j`.

Use `congrFun (hc' j) k` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Introduce `i j hij`. Conclude with `hc j i (by simpa using hij)`. Introduce `v hv`.

Establish `hz : Matrix.mulVec (X₂.conjTranspose * J) v = 0`. Use function extensionality and compare the values at `i`. Rewrite using `[hcol]`. Conclude with `hv _ (by simp)`. Take `⟨w, a, hwa⟩` from `hperp v hz`.

Use `⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) + (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Assume the negation of the conclusion as `hc`. Establish `hc' : ¬ i.val < l` using `by omega`. Conclude with `hi (by simp [hc, hc'])`.

Rewrite using `[hwa, Matrix.mulVec_add, he1, he2]`.
-/
theorem isotropic_unipotent_column_relations : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  intro n r J X hX l d h u A X₁ Xb X₂ h1 hb hperp
  classical

  have hext : ∀ (m : ℕ) (hm : m ≤ r) (a : Fin m → ℂ),
      Matrix.mulVec X (fun i : Fin r => if hi : i.val < m then a ⟨i.val, hi⟩ else 0) =
        Matrix.mulVec (X.submatrix id fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) a := by
    intro m hm a
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    symm
    refine Fintype.sum_of_injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) ?_ _ _ ?_ ?_
    · intro x y hxy
      exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro i hi
      have : ¬ i.val < m := by
        intro hlt
        exact hi ⟨⟨i.val, hlt⟩, rfl⟩
      simp [this]
    · intro j
      simp
  have he1 : ∀ a : Fin l → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₁ a := fun a => hext l (by omega) a
  have he2 : ∀ a : Fin (l + d) → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l + d then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₂ a := fun a => hext (l + d) h a
  have hcol : ∀ (v : Fin n → ℂ) (i : Fin (l + d)),
      Matrix.mulVec (X₂.conjTranspose * J) v i =
        Matrix.mulVec (X.conjTranspose * J) v ⟨i.val, by omega⟩ := by
    intro v i
    rfl
  have hXc : ∀ (i j : Fin r), Matrix.mulVec (X.conjTranspose * J) (fun k => X k j) i = 0 := by
    intro i j
    exact congrFun (congrFun hX i) j
  have key : ∀ j : Fin r, ∃ c : Fin r → ℂ,
      (∀ i, c i ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
      Matrix.mulVec u (fun k => X k j) = (fun k => X k j) + Matrix.mulVec X c := by
    intro j
    by_cases hj1 : j.val < l
    · refine ⟨0, fun i hi => absurd rfl hi, ?_⟩
      funext k
      have := congrFun (congrFun h1 k) ⟨j.val, hj1⟩
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, X₁] using this
    by_cases hj2 : j.val < l + d
    · refine ⟨fun i => if hi : i.val < l then A ⟨i.val, hi⟩ ⟨j.val - l, by omega⟩ else 0, ?_, ?_⟩
      · intro i hi
        left
        by_cases hil : i.val < l
        · exact ⟨hil, by omega⟩
        · exact absurd (by simp [hil]) hi
      · have he1' := he1 (fun i => A i ⟨j.val - l, by omega⟩)
        beta_reduce at he1'
        rw [he1']
        funext k
        have := congrFun (congrFun hb k) ⟨j.val - l, by omega⟩
        have hjj : (⟨l + (j.val - l), by omega⟩ : Fin r) = j := Fin.ext (by simp; omega)
        simp only [Matrix.mul_apply, Matrix.add_apply, Xb, X₁, Matrix.submatrix_apply, id, hjj] at this
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, X₁] using this
    · have hz : Matrix.mulVec (X₂.conjTranspose * J) (fun k => X k j) = 0 := by
        funext i
        rw [hcol]
        exact hXc _ _
      obtain ⟨w, a, hwa⟩ := hperp _ hz
      refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
          (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
      · intro i hi
        right
        refine ⟨?_, by omega⟩
        by_contra hc
        have hc' : ¬ i.val < l := by omega
        exact hi (by simp [hc, hc'])
      · rw [Matrix.mulVec_add, he1, he2, ← hwa]
        abel
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, ?_, ?_, ?_⟩
  · ext k j
    have := congrFun (hc' j) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro i j hij
    exact hc j i (by simpa using hij)
  · intro v hv
    have hz : Matrix.mulVec (X₂.conjTranspose * J) v = 0 := by
      funext i
      rw [hcol]
      exact hv _ (by simp)
    obtain ⟨w, a, hwa⟩ := hperp v hz
    refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
        (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
    · intro i hi
      by_contra hc
      have hc' : ¬ i.val < l := by omega
      exact hi (by simp [hc, hc'])
    · rw [hwa, Matrix.mulVec_add, he1, he2]

end GlobalTheory
