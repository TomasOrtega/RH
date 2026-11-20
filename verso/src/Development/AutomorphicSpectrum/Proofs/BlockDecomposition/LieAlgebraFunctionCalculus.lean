import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.AdProj

noncomputable def entryMul {n : ℕ} (h : Fin n → ℝ) (g : ℝ → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (g (h i - h j) : ℂ) * X i j

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diagonal_commutator {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by
  ext i j
  simp only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `h0 : entryMul h (fun t => t ^ 0) X = X`. Use extensionality with `i j`. Simplify using `[entryMul]`.

Rewrite using `[h0]`. Conclude with `hX`. Consider the case `succ k ih`. Establish `hs : entryMul h (fun t => t ^ (k + 1)) X = Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X - entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ))`. Rewrite using `[diagonal_commutator]`.

Use extensionality with `i j`. Simplify using `only [entryMul, Matrix.of_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`.

Conclude with `hbr _ hD _ ih`.
-/
theorem entryMul_pow_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (k : ℕ) :
    entryMul h (fun t => t ^ k) X ∈ 𝔤 := by
  induction k with
  | zero =>
    have h0 : entryMul h (fun t => t ^ 0) X = X := by
      ext i j
      simp [entryMul]
    rw [h0]
    exact hX
  | succ k ih =>
    have hs : entryMul h (fun t => t ^ (k + 1)) X =
        Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X -
          entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ)) := by
      rw [diagonal_commutator]
      ext i j
      simp only [entryMul, Matrix.of_apply]
      push_cast
      ring
    rw [hs]
    exact hbr _ hD _ ih

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Establish `hs : entryMul h (fun t => (p + q).eval t) X = entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X`. Use extensionality with `i j`. Simplify using `only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`. Conclude with `𝔤.add_mem hp hq`. Consider the case `monomial m a`.

Establish `hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X = a • entryMul h (fun t => t ^ m) X`. Use extensionality with `i j`. Simplify using `only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hs]`. Conclude with `𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)`.
-/
theorem entryMul_poly_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : entryMul h (fun t => (p + q).eval t) X =
        entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]
      push_cast
      ring
    rw [hs]
    exact 𝔤.add_mem hp hq
  | monomial m a =>
    have hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X =
        a • entryMul h (fun t => t ^ m) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial,
        Complex.real_smul]
      push_cast
      ring
    rw [hs]
    exact 𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)

/- English proof (translation)
Introduce `hD hbr f X hX`. Take `⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S` from `⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2), fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩`. Establish `key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x` using `fun x hx => Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx`. Take `⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j)` from `⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩`. Establish `heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X`.

Use extensionality with `i j`. Simplify using `only [entryMul, Matrix.of_apply, hp]`. Rewrite using `[heq]`. Conclude with `entryMul_poly_mem 𝔤 h hD hbr hX p`.
-/
theorem mem_of_entrywise {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  intro hD hbr f X hX
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S :=
    ⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2),
      fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩
  have key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j) :=
    ⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩
  have heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X := by
    ext i j
    simp only [entryMul, Matrix.of_apply, hp]
  rw [heq]
  exact entryMul_poly_mem 𝔤 h hD hbr hX p

end GlobalTheory.CompanionTheory.AdProj
