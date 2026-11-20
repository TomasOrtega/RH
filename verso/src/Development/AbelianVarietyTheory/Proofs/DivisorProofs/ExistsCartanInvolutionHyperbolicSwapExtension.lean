import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneCartan
open Matrix

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem entry_eq {n : ℕ} {k l : Type} [Fintype k] [Fintype l] (A : Matrix (Fin n) k ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) l ℂ) (j : k) (m : l) :
    (Aᵀ * M * B) j m = (fun i => A i j) ⬝ᵥ M *ᵥ (fun i => B i m) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Establish `h : ∀ i j, M i j = star (M j i)` using `fun i j => by`. Use `congrFun (congrFun hM i) j` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_apply]`. Conclude with `this.symm`. Simplify using `only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h j i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.conjTranspose = M) (x y : Fin n → ℂ) :
    x ⬝ᵥ M *ᵥ star y = star (y ⬝ᵥ M *ᵥ star x) := by
  have h : ∀ i j, M i j = star (M j i) := fun i j => by
    have := congrFun (congrFun hM i) j
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h j i]; ring

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]`.
-/
theorem star_mulVec' {n : ℕ} {k : Type} [Fintype k] (P : Matrix (Fin n) k ℂ) (b : k → ℂ) :
    star (P *ᵥ b) = P.map star *ᵥ star b := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, star_sum, mul_comm]`.
-/
theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum, mul_comm]

/- English proof (translation)
Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]`.
-/
theorem dot_mulVec_left {n : ℕ} {k : Type} [Fintype k] (P : Matrix (Fin n) k ℂ) (a : k → ℂ) (v : Fin n → ℂ) :
    (P *ᵥ a) ⬝ᵥ v = a ⬝ᵥ (Pᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

/- English proof (translation)
Establish `key : ∀ a b : k → ℂ, (P *ᵥ a) ⬝ᵥ M *ᵥ star (P *ᵥ b) = a ⬝ᵥ G *ᵥ star b`. Introduce `a b`. Rewrite using `[star_mulVec', dot_mulVec_left, ← hG, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul, map_star_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `x hx`. Establish `hx' : x = P *ᵥ (Q *ᵥ x)` using `by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]`. Establish `hy : Q *ᵥ x ≠ 0`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hx', h, Matrix.mulVec_zero]`. Establish `e1 : (P * D * Q) *ᵥ x = P *ᵥ (D *ᵥ (Q *ᵥ x))` using `by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `e2 : (P *ᵥ (D *ᵥ (Q *ᵥ x))) ⬝ᵥ M *ᵥ star x = (D *ᵥ (Q *ᵥ x)) ⬝ᵥ G *ᵥ star (Q *ᵥ x)`.

Use `key (D *ᵥ (Q *ᵥ x)) (Q *ᵥ x)` as an intermediate fact. Rewrite `this` using `[← hx']`. Then use the resulting hypothesis. Rewrite using `[e1, e2]`. Conclude with `hD3 _ hy`.
-/
theorem transport {n : ℕ} {k : Type} [Fintype k] [DecidableEq k] (M : Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) k ℂ) (Q : Matrix k (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (G D : Matrix k k ℂ) (hG : Pᵀ * M * P.map star = G) (hD1 : D * D = 1) (hD2 : Dᵀ * G * D.map star = G)
    (hD3 : ∀ y : k → ℂ, y ≠ 0 → 0 < ((D *ᵥ y) ⬝ᵥ G *ᵥ star y).re) : IsCartan M (P * D * Q) := by
  have key : ∀ a b : k → ℂ, (P *ᵥ a) ⬝ᵥ M *ᵥ star (P *ᵥ b) = a ⬝ᵥ G *ᵥ star b := by
    intro a b
    rw [star_mulVec', dot_mulVec_left, ← hG, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · calc P * D * Q * (P * D * Q) = P * D * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P D D, hD1, Matrix.mul_one, hPQ]
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul, map_star_mul]
    calc Qᵀ * (Dᵀ * Pᵀ) * M * (P.map star * D.map star * Q.map star)
        = Qᵀ * (Dᵀ * (Pᵀ * M * P.map star) * D.map star) * Q.map star := by simp only [Matrix.mul_assoc]
      _ = Qᵀ * (Pᵀ * M * P.map star) * Q.map star := by rw [hG, hD2]
      _ = (P * Q)ᵀ * M * (P * Q).map star := by rw [Matrix.transpose_mul, map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by rw [hPQ]; simp
  · intro x hx
    have hx' : x = P *ᵥ (Q *ᵥ x) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    have hy : Q *ᵥ x ≠ 0 := by
      intro h; apply hx; rw [hx', h, Matrix.mulVec_zero]
    have e1 : (P * D * Q) *ᵥ x = P *ᵥ (D *ᵥ (Q *ᵥ x)) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (P *ᵥ (D *ᵥ (Q *ᵥ x))) ⬝ᵥ M *ᵥ star x = (D *ᵥ (Q *ᵥ x)) ⬝ᵥ G *ᵥ star (Q *ᵥ x) := by
      have := key (D *ᵥ (Q *ᵥ x)) (Q *ᵥ x)
      rwa [← hx'] at this
    rw [e1, e2]
    exact hD3 _ hy

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

def swapI : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def hypI : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; -Complex.I, 0]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem swapI_mul : swapI * swapI = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, hypI, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem swapI_iso : swapIᵀ * hypI * swapI.map star = hypI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, hypI, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[swapI, hypI, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_conj]`. Rewrite using `[← Complex.mul_conj, ← Complex.mul_conj]`. Take the linear combination `(-(y 1 * (starRingEnd ℂ) (y 1) + y 0 * (starRingEnd ℂ) (y 0))) * Complex.I_mul_I`.
-/
theorem swapI_pos (y : Fin 2 → ℂ) : ((swapI *ᵥ y) ⬝ᵥ hypI *ᵥ star y) = (Complex.normSq (y 0) + Complex.normSq (y 1) : ℂ) := by
  simp [swapI, hypI, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_conj]
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  linear_combination (-(y 1 * (starRingEnd ℂ) (y 1) + y 0 * (starRingEnd ℂ) (y 0))) * Complex.I_mul_I

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.fromBlocks_multiply, h1, swapI_mul]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`.

Simplify using `only [Matrix.transpose_zero, Matrix.map_zero _ (star_zero ℂ), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Rewrite using `[h2, swapI_iso]`. Introduce `y hy`. Establish `key : ((Matrix.fromBlocks θ₁ 0 0 swapI) *ᵥ y) ⬝ᵥ Matrix.fromBlocks G₁ 0 0 hypI *ᵥ star y = (θ₁ *ᵥ (y ∘ Sum.inl)) ⬝ᵥ G₁ *ᵥ star (y ∘ Sum.inl) + (swapI *ᵥ (y ∘ Sum.inr)) ⬝ᵥ hypI *ᵥ star (y ∘ Sum.inr)`. Simplify using `[dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Pi.star_apply]`.

Both sides reduce to the same expression. Rewrite using `[key, Complex.add_re, swapI_pos]`. Simplify using `only [Function.comp_apply]`. Establish `hn : ((Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1)) : ℂ)).re = Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1))`. Simplify using the standard rewrite rules.

Rewrite using `[hn]`. Establish `n0` using `Complex.normSq_nonneg (y (Sum.inr 0))`. Establish `n1` using `Complex.normSq_nonneg (y (Sum.inr 1))`. Distinguish the cases in `h0 : y ∘ Sum.inl = 0`. Establish `hc : y (Sum.inr 0) ≠ 0 ∨ y (Sum.inr 1) ≠ 0`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hy` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Conclude with `congrFun h0 i`. Use `fin_cases i`. Conclude with `hc.1`. Conclude with `hc.2`. Rewrite using `[h0]`.

Simplify using `only [star_zero, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, zero_add]`. Break down `hc with h | h` into its components or cases. Use `Complex.normSq_pos.2 h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Complex.normSq_pos.2 h` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `h3 _ h0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem blk_cartan {m : ℕ} (G₁ θ₁ : Matrix (Fin m) (Fin m) ℂ) (h : IsCartan G₁ θ₁) :
    (Matrix.fromBlocks θ₁ 0 0 swapI) * (Matrix.fromBlocks θ₁ 0 0 swapI) = 1 ∧
    (Matrix.fromBlocks θ₁ 0 0 swapI)ᵀ * Matrix.fromBlocks G₁ 0 0 hypI * (Matrix.fromBlocks θ₁ 0 0 swapI).map star =
      Matrix.fromBlocks G₁ 0 0 hypI ∧
    ∀ y : Fin m ⊕ Fin 2 → ℂ, y ≠ 0 →
      0 < (((Matrix.fromBlocks θ₁ 0 0 swapI) *ᵥ y) ⬝ᵥ Matrix.fromBlocks G₁ 0 0 hypI *ᵥ star y).re := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply, h1, swapI_mul]; simp
  · rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.map_zero _ (star_zero ℂ), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [h2, swapI_iso]
  · intro y hy
    have key : ((Matrix.fromBlocks θ₁ 0 0 swapI) *ᵥ y) ⬝ᵥ Matrix.fromBlocks G₁ 0 0 hypI *ᵥ star y =
        (θ₁ *ᵥ (y ∘ Sum.inl)) ⬝ᵥ G₁ *ᵥ star (y ∘ Sum.inl) + (swapI *ᵥ (y ∘ Sum.inr)) ⬝ᵥ hypI *ᵥ star (y ∘ Sum.inr) := by
      simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Pi.star_apply]
      rfl
    rw [key, Complex.add_re, swapI_pos]
    simp only [Function.comp_apply]
    have hn : ((Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1)) : ℂ)).re =
        Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1)) := by
      simp
    rw [hn]
    have n0 := Complex.normSq_nonneg (y (Sum.inr 0))
    have n1 := Complex.normSq_nonneg (y (Sum.inr 1))
    by_cases h0 : y ∘ Sum.inl = 0
    · have hc : y (Sum.inr 0) ≠ 0 ∨ y (Sum.inr 1) ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply hy; funext i; rcases i with i | i
        · exact congrFun h0 i
        · fin_cases i
          · exact hc.1
          · exact hc.2
      rw [h0]
      simp only [star_zero, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, zero_add]
      rcases hc with h | h
      · have := Complex.normSq_pos.2 h; linarith
      · have := Complex.normSq_pos.2 h; linarith
    · have := h3 _ h0
      linarith

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

noncomputable def cols {n₁ : ℕ} (X Y : Fin (n₁ + 2) → ℂ) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) :
    Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) ℂ :=
  Matrix.fromCols ι (Matrix.of fun i k => (![X, Y] k) i)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[cols, Matrix.fromCols_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cols_mulVec {n₁ : ℕ} (X Y : Fin (n₁ + 2) → ℂ) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (w : Fin n₁ ⊕ Fin 2 → ℂ) :
    cols X Y ι *ᵥ w = ι *ᵥ (w ∘ Sum.inl) + w (Sum.inr 0) • X + w (Sum.inr 1) • Y := by
  ext i
  simp [cols, Matrix.fromCols_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  ring

/- English proof (translation)
Establish `c1 : ∀ a, (fun i => cols X Y ι i (Sum.inl a)) = ι *ᵥ Pi.single a 1` using `fun a => by`. Use extensionality with `i`. Simplify using `[cols, Matrix.mulVec_single_one]`. Establish `c2 : (fun i => cols X Y ι i (Sum.inr 0)) = X` using `by ext i; simp [cols]`. Establish `c3 : (fun i => cols X Y ι i (Sum.inr 1)) = Y` using `by ext i; simp [cols]`.

Establish `s1 : ∀ a, (fun i => (cols X Y ι).map star i (Sum.inl a)) = star (ι *ᵥ Pi.single a 1)` using `fun a => by`. Use extensionality with `i`. Simplify using `[cols, Matrix.mulVec_single_one]`. Establish `s2 : (fun i => (cols X Y ι).map star i (Sum.inr 0)) = star X` using `by ext i; simp [cols]`. Establish `s3 : (fun i => (cols X Y ι).map star i (Sum.inr 1)) = star Y` using `by ext i; simp [cols]`.

Use extensionality with `(a | a) (b | b)`. Rewrite using `[entry_eq, Matrix.fromBlocks_apply₁₁, entry_eq]`. Both sides reduce to the same expression. Rewrite using `[entry_eq, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] fin_cases b`. Conclude with `(c1 a ▸ s2 ▸ (hι _).1 : _)`.

Conclude with `(c1 a ▸ s3 ▸ (hι _).2 : _)`. Rewrite using `[entry_eq, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] fin_cases a`. Use `show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0`. Rewrite using `[c2, s1, form_symm hM, (hι _).1, star_zero]`. Use `show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0`.

Rewrite using `[c3, s1, form_symm hM, (hι _).2, star_zero]`. Apply the tactic sequence `rw [entry_eq, Matrix.fromBlocks_apply₂₂] fin_cases a <;> fin_cases b`. Use `show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 0 0`. Rewrite using `[c2, s2, hXX]`. Simplify using `[hypI]`.

Use `show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 0 1`. Rewrite using `[c2, s3, hXY]`. Simplify using `[hypI]`. Use `show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 1 0`. Rewrite using `[c3, s2, form_symm hM, hXY]`.

Simplify using `[hypI]`. Use `show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 1 1`. Rewrite using `[c3, s3, hYY]`. Simplify using `[hypI]`.
-/
theorem cols_gram {n₁ : ℕ} (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (hM : M.conjTranspose = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = Complex.I)
    (hι : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) :
    (cols X Y ι)ᵀ * M * (cols X Y ι).map star = Matrix.fromBlocks (ιᵀ * M * ι.map star) 0 0 hypI := by
  have c1 : ∀ a, (fun i => cols X Y ι i (Sum.inl a)) = ι *ᵥ Pi.single a 1 := fun a => by
    ext i; simp [cols, Matrix.mulVec_single_one]
  have c2 : (fun i => cols X Y ι i (Sum.inr 0)) = X := by ext i; simp [cols]
  have c3 : (fun i => cols X Y ι i (Sum.inr 1)) = Y := by ext i; simp [cols]
  have s1 : ∀ a, (fun i => (cols X Y ι).map star i (Sum.inl a)) = star (ι *ᵥ Pi.single a 1) := fun a => by
    ext i; simp [cols, Matrix.mulVec_single_one]
  have s2 : (fun i => (cols X Y ι).map star i (Sum.inr 0)) = star X := by ext i; simp [cols]
  have s3 : (fun i => (cols X Y ι).map star i (Sum.inr 1)) = star Y := by ext i; simp [cols]
  ext (a | a) (b | b)
  · rw [entry_eq, Matrix.fromBlocks_apply₁₁, entry_eq]; rfl
  · rw [entry_eq, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    fin_cases b
    · exact (c1 a ▸ s2 ▸ (hι _).1 : _)
    · exact (c1 a ▸ s3 ▸ (hι _).2 : _)
  · rw [entry_eq, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    fin_cases a
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0
      rw [c2, s1, form_symm hM, (hι _).1, star_zero]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0
      rw [c3, s1, form_symm hM, (hι _).2, star_zero]
  · rw [entry_eq, Matrix.fromBlocks_apply₂₂]
    fin_cases a <;> fin_cases b
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 0 0
      rw [c2, s2, hXX]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 0 1
      rw [c2, s3, hXY]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 1 0
      rw [c3, s2, form_symm hM, hXY]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 1 1
      rw [c3, s3, hYY]; simp [hypI]

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

/- English proof (translation)
Rewrite `h` using `[cols_mulVec]`. Establish `hYX : Y ⬝ᵥ M *ᵥ star X = -Complex.I` using `by rw [form_symm hM, hXY]; simp`. Establish `hX` using `congrArg (· ⬝ᵥ M *ᵥ star X) h`. Establish `hY` using `congrArg (· ⬝ᵥ M *ᵥ star Y) h`. Simplify using `only [add_dotProduct, smul_dotProduct, zero_dotProduct, (hι _).1, (hι _).2, hXX, hYY, hXY, hYX, smul_eq_mul] at hX hY`.

Establish `hb : w (Sum.inr 1) = 0`. Establish `: w (Sum.inr 1) * Complex.I = 0` using `by linear_combination -hX`. Simplify `this` using `[Complex.I_ne_zero]`. Establish `ha : w (Sum.inr 0) = 0`. Establish `: w (Sum.inr 0) * Complex.I = 0` using `by linear_combination hY`.

Simplify `this` using `[Complex.I_ne_zero]`. Rewrite `h` using `[ha, hb, zero_smul, zero_smul, add_zero, add_zero]`. Establish `hu : w ∘ Sum.inl = 0` using `hinj (by rw [h, Matrix.mulVec_zero])`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Conclude with `congrFun hu i`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb`.
-/
theorem cols_ker {n₁ : ℕ} (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (hM : M.conjTranspose = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = Complex.I)
    (hι : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) (hinj : Function.Injective ι.mulVec)
    (w : Fin n₁ ⊕ Fin 2 → ℂ) (h : cols X Y ι *ᵥ w = 0) : w = 0 := by
  rw [cols_mulVec] at h
  have hYX : Y ⬝ᵥ M *ᵥ star X = -Complex.I := by rw [form_symm hM, hXY]; simp
  have hX := congrArg (· ⬝ᵥ M *ᵥ star X) h
  have hY := congrArg (· ⬝ᵥ M *ᵥ star Y) h
  simp only [add_dotProduct, smul_dotProduct, zero_dotProduct, (hι _).1, (hι _).2, hXX, hYY, hXY, hYX,
    smul_eq_mul] at hX hY
  have hb : w (Sum.inr 1) = 0 := by
    have : w (Sum.inr 1) * Complex.I = 0 := by linear_combination -hX
    simpa [Complex.I_ne_zero] using this
  have ha : w (Sum.inr 0) = 0 := by
    have : w (Sum.inr 0) * Complex.I = 0 := by linear_combination hY
    simpa [Complex.I_ne_zero] using this
  rw [ha, hb, zero_smul, zero_smul, add_zero, add_zero] at h
  have hu : w ∘ Sum.inl = 0 := hinj (by rw [h, Matrix.mulVec_zero])
  funext i
  rcases i with i | i
  · exact congrFun hu i
  · fin_cases i
    · exact ha
    · exact hb

/- English proof (translation)
Introduce `n₁ M X Y ι θ₁ hM hXX hYY hXY hι hinj hθ₁`. Use `set P := cols X Y ι with hP`. Set `e : Fin n₁ ⊕ Fin 2 ≃ Fin (n₁ + 2)` to `finSumFinEquiv`. Use `set P' : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := P.submatrix id e.symm with hP'`. Establish `hPP' : P = P'.submatrix id e` using `by ext i j; simp [hP']`.

Establish `hinj' : Function.Injective P'.mulVec`. Introduce `v v' hv`. Establish `h0 : P' *ᵥ (v - v') = 0` using `by rw [Matrix.mulVec_sub, hv, sub_self]`. Rewrite `h0` using `[hP', Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]`. Establish `h1 : P *ᵥ ((v - v') ∘ e) = 0` using `by simpa using h0`.

Establish `h2` using `cols_ker M X Y ι hM hXX hYY hXY hι hinj _ h1`. Establish `h3 : v - v' = 0`. Use function extensionality and compare the values at `i`. Use `congrFun h2 (e.symm i)` as an intermediate fact. Simplify using `using this`.

Conclude with `sub_eq_zero.1 h3`. Establish `hU : IsUnit P'.det` using `(Matrix.isUnit_iff_isUnit_det P').1 (Matrix.mulVec_injective_iff_isUnit.1 hinj')`. Use `set Q : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) ℂ := (P'⁻¹).submatrix e id with hQ`. Establish `hPQ : P * Q = 1`. Rewrite using `[hPP', hQ, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hU]`.

Simplify using the standard rewrite rules. Establish `hQP : Q * P = 1`. Rewrite using `[hPP', hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ hU]`. Conclude with `Matrix.submatrix_one_equiv e`. Use `set D : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) ℂ := Matrix.fromBlocks θ₁ 0 0 swapI with hD`.

Take `⟨hD1, hD2, hD3⟩` from `blk_cartan _ _ hθ₁`. Establish `hG` using `cols_gram M X Y ι hM hXX hYY hXY hι`. Use `⟨P * D * Q, transport M P Q hPQ hQP _ D hG hD1 hD2 hD3, ?_, -Complex.I, by simp, ?_⟩` and prove the remaining obligations. Use `set E : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁) ℂ := Matrix.fromRows (1 : Matrix (Fin n₁) (Fin n₁) ℂ) (0 : Matrix (Fin 2) (Fin n₁) ℂ) with hEdef`. Establish `hE : P * E = ι`.

Use extensionality with `i j`. Simplify using `[hP, hEdef, cols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`. Establish `hDE : D * E = E * θ₁`. Apply the tactic sequence `ext (i | i) j <;> simp [hD, hEdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hE]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = P * (D * E) := by`. Rewrite using `[hQP, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = ι * θ₁ := by rw [hDE, ← Matrix.mul_assoc, hE]`.

Establish `hz : ∀ k : Fin 2, (Pi.single (Sum.inr k) (1 : ℂ) : Fin n₁ ⊕ Fin 2 → ℂ) ∘ Sum.inl = 0` using `fun k => by`. Use function extensionality and compare the values at `m`. Simplify using the standard rewrite rules. Establish `hX : X = P *ᵥ Pi.single (Sum.inr 0) 1`. Rewrite using `[hP, cols_mulVec, hz, Matrix.mulVec_zero]`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hY : Y = P *ᵥ Pi.single (Sum.inr 1) 1`. Rewrite using `[hP, cols_mulVec, hz, Matrix.mulVec_zero]`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Establish `hDs : D *ᵥ Pi.single (Sum.inr 0) 1 = Complex.I • Pi.single (Sum.inr 1) 1`. Use extensionality with `(i | i)`. Simplify using `[hD, Matrix.fromBlocks_mulVec]`. Apply the tactic sequence `fin_cases i <;> simp [hD, Matrix.fromBlocks_mulVec, swapI, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`.

Establish `: (P * D * Q) *ᵥ X = Complex.I • Y`. Rewrite using `[hX, Matrix.mulVec_mulVec, show P * D * Q * P = P * D * (Q * P) by simp only [Matrix.mul_assoc], hQP, Matrix.mul_one, ← Matrix.mulVec_mulVec, hDs, Matrix.mulVec_smul, ← hY]`. Rewrite using `[this, smul_smul]`. Simplify using the standard rewrite rules.
-/
theorem exists_cartan_hyperbolic_swap : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  intro n₁ M X Y ι θ₁ hM hXX hYY hXY hι hinj hθ₁
  set P := cols X Y ι with hP
  let e : Fin n₁ ⊕ Fin 2 ≃ Fin (n₁ + 2) := finSumFinEquiv
  set P' : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := P.submatrix id e.symm with hP'
  have hPP' : P = P'.submatrix id e := by ext i j; simp [hP']
  have hinj' : Function.Injective P'.mulVec := by
    intro v v' hv
    have h0 : P' *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, hv, sub_self]
    rw [hP', Matrix.submatrix_mulVec_equiv, Equiv.symm_symm] at h0
    have h1 : P *ᵥ ((v - v') ∘ e) = 0 := by simpa using h0
    have h2 := cols_ker M X Y ι hM hXX hYY hXY hι hinj _ h1
    have h3 : v - v' = 0 := by
      funext i
      have := congrFun h2 (e.symm i)
      simpa using this
    exact sub_eq_zero.1 h3
  have hU : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 (Matrix.mulVec_injective_iff_isUnit.1 hinj')
  set Q : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) ℂ := (P'⁻¹).submatrix e id with hQ
  have hPQ : P * Q = 1 := by
    rw [hPP', hQ, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hU]
    simp
  have hQP : Q * P = 1 := by
    rw [hPP', hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ hU]
    exact Matrix.submatrix_one_equiv e
  set D : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) ℂ := Matrix.fromBlocks θ₁ 0 0 swapI with hD
  obtain ⟨hD1, hD2, hD3⟩ := blk_cartan _ _ hθ₁
  have hG := cols_gram M X Y ι hM hXX hYY hXY hι
  refine ⟨P * D * Q, transport M P Q hPQ hQP _ D hG hD1 hD2 hD3, ?_, -Complex.I, by simp, ?_⟩
  · set E : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁) ℂ :=
      Matrix.fromRows (1 : Matrix (Fin n₁) (Fin n₁) ℂ) (0 : Matrix (Fin 2) (Fin n₁) ℂ) with hEdef
    have hE : P * E = ι := by
      ext i j; simp [hP, hEdef, cols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hDE : D * E = E * θ₁ := by
      ext (i | i) j <;> simp [hD, hEdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    calc P * D * Q * ι = P * D * (Q * P) * E := by
          rw [← hE]; simp only [Matrix.mul_assoc]
      _ = P * (D * E) := by
          rw [hQP, Matrix.mul_one, Matrix.mul_assoc]
      _ = ι * θ₁ := by rw [hDE, ← Matrix.mul_assoc, hE]
  · have hz : ∀ k : Fin 2, (Pi.single (Sum.inr k) (1 : ℂ) : Fin n₁ ⊕ Fin 2 → ℂ) ∘ Sum.inl = 0 := fun k => by
      funext m; simp
    have hX : X = P *ᵥ Pi.single (Sum.inr 0) 1 := by
      rw [hP, cols_mulVec, hz, Matrix.mulVec_zero]; ext i; simp
    have hY : Y = P *ᵥ Pi.single (Sum.inr 1) 1 := by
      rw [hP, cols_mulVec, hz, Matrix.mulVec_zero]; ext i; simp
    have hDs : D *ᵥ Pi.single (Sum.inr 0) 1 = Complex.I • Pi.single (Sum.inr 1) 1 := by
      ext (i | i)
      · simp [hD, Matrix.fromBlocks_mulVec]
      · fin_cases i <;> simp [hD, Matrix.fromBlocks_mulVec, swapI, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have : (P * D * Q) *ᵥ X = Complex.I • Y := by
      rw [hX, Matrix.mulVec_mulVec, show P * D * Q * P = P * D * (Q * P) by simp only [Matrix.mul_assoc], hQP,
        Matrix.mul_one, ← Matrix.mulVec_mulVec, hDs, Matrix.mulVec_smul, ← hY]
    rw [this, smul_smul]
    simp

end GlobalTheory.PlaneCartan
