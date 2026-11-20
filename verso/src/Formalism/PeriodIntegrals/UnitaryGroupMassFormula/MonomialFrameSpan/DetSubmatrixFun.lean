import Mathlib

open Matrix Finset

noncomputable section

namespace GenFrameSpan

/- English proof (translation)
Simplify using `only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.submatrix_apply, id, Finset.smul_sum, Finset.mul_sum, Finset.prod_mul_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Units.smul_def, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Matrix.submatrix_apply, id, Finset.smul_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

/- English proof (translation)
Distinguish the cases in `hf : Function.Injective f`. Use `right set s := Finset.univ.image f with hs`. Establish `hcard : s.card = p`. Rewrite using `[hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]`. Set `J` to `s.orderEmbOfFin hcard`.

Establish `hmem : ∀ i, f i ∈ Set.range J`. Introduce `i`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using `[hs]`. Use `choose g hg using hmem`.

Establish `hginj : Function.Injective g`. Introduce `a b h`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← hg a, ← hg b, h]`. Set `σ : Equiv.Perm (Fin p)` to `Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)`.

Use `⟨J, (Equiv.Perm.sign σ : ℤ), ?_⟩` and prove the remaining obligations. Establish `e : M.submatrix id f = (M.submatrix id J).submatrix id σ`. Use extensionality with `a b`. Simplify using `[σ, hg]`. Rewrite using `[e, Matrix.det_permute']`.

Apply the tactic sequence `try norm_cast`. Use `left`. Rewrite `hf` using `[Function.Injective]`. Use `push_neg at hf`. Take `⟨i, j, hij, hne⟩` from `hf`.

Conclude with `Matrix.det_zero_of_column_eq hne (fun a => by simp [hij])`.
-/
theorem det_submatrix_fun {R : Type*} [CommRing R] {p n : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (f : Fin p → Fin n) :
    (M.submatrix id f).det = 0 ∨ ∃ (J : Fin p ↪o Fin n) (e : ℤ),
      (M.submatrix id f).det = (e : R) * (M.submatrix id J).det := by
  classical
  by_cases hf : Function.Injective f
  · right
    set s := Finset.univ.image f with hs
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let J := s.orderEmbOfFin hcard
    have hmem : ∀ i, f i ∈ Set.range J := by
      intro i
      rw [Finset.range_orderEmbOfFin]
      simp [hs]
    choose g hg using hmem
    have hginj : Function.Injective g := by
      intro a b h
      apply hf
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin p) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
    refine ⟨J, (Equiv.Perm.sign σ : ℤ), ?_⟩
    have e : M.submatrix id f = (M.submatrix id J).submatrix id σ := by
      ext a b
      simp [σ, hg]
    rw [e, Matrix.det_permute']
    try norm_cast
  · left
    rw [Function.Injective] at hf
    push_neg at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hij])

end GenFrameSpan
