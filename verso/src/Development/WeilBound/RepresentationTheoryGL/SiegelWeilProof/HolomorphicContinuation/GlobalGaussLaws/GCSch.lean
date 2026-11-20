import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GCSchH

/- English proof (translation)
Introduce `m n ε t c hc htc Z Z' hZ hZ'`. Use `set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS`. Use `set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'`. Use `set B := qB S S' c Z Z' with hB`. Establish `hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u))`.

Use function extensionality and compare the values at `u`. Simplify using `only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]`. Both sides reduce to the same expression. Establish `hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef`. Establish `h` using `hZ.transpose`.

Rewrite `h` using `[Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose]`. Then use the resulting hypothesis. Establish `hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef`. Establish `h` using `hZ'.transpose`. Unfold `IsSiegel at h`. Rewrite `h` using `[Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose]`.

Rewrite using `[Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]` and apply the resulting hypothesis. Establish `hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re)`. Introduce `u`. Rewrite using `[hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]`. Establish `e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im`.

Introduce `a`. Rewrite using `[Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]`. Simplify using `only [e2, Finset.sum_neg_distrib, im_quad]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re`.

Introduce `u hu`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hu`. Rewrite using `[hre]`. Apply `mul_pos hc` to reduce the goal to its premises. Establish `n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re` using `Finset.sum_nonneg fun a _ => quad_nonneg hP1 _`.

Establish `n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re` using `Finset.sum_nonneg fun a _ => quad_nonneg hP2 _`. Consider the cases of `hb : epsT t ε a`. Establish `haS : a ∈ S'` using `by simp [hS', hb]`. Establish `p2` using `Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `haS : a ∈ S` using `by simp [hS, hb]`. Establish `p1` using `Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨κ, hκ, hco⟩` from `coercive_of_pos B hpos`. Take `⟨g, hg, -⟩` from `GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[hgC]`. Use function extensionality and compare the values at `u`. Conclude with `hg u`.
-/
theorem gCSch : GCSch := by
  intro m n ε t c hc htc Z Z' hZ hZ'
  set S := Finset.univ.filter (fun a => epsT t ε a = true) with hS
  set S' := Finset.univ.filter (fun a => epsT t ε a = false) with hS'
  set B := qB S S' c Z Z' with hB
  have hgC : gC ε t c Z Z' = fun u => Complex.exp (-(B u u)) := by
    funext u
    simp only [gC, hB, qB_apply, qF, neg_neg, trace_gramB]
    rfl
  have hP1 : ((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)).PosDef := by
    have h := hZ.transpose
    rwa [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.conjTranspose_transpose] at h
  have hP2 : ((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)).PosDef := by
    have h := hZ'.transpose
    unfold IsSiegel at h
    rw [Matrix.conjTranspose_conjTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.conjTranspose_transpose] at h
    rwa [Matrix.conjTranspose_neg, sub_neg_eq_add, neg_add_eq_sub]
  have hre : ∀ u : Fin m → Fin n → ℂ, (B u u).re = c * (∑ a ∈ S, (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re + ∑ a ∈ S', (star (u a) ⬝ᵥ
      (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re) := by
    intro u
    rw [hB, qB_apply, qF, Complex.neg_re, Complex.sub_re, re_I_mul, re_I_mul, Complex.im_sum, Complex.im_sum]
    have e2 : ∀ a, (star (u a) ⬝ᵥ (Z'ᵀ *ᵥ u a)).im = -(star (u a) ⬝ᵥ ((-Z'ᵀ) *ᵥ u a)).im := by
      intro a; rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_im, neg_neg]
    simp only [e2, Finset.sum_neg_distrib, im_quad]
    ring
  have hpos : ∀ u : Fin m → Fin n → ℂ, u ≠ 0 → 0 < (B u u).re := by
    intro u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
    rw [hre]
    apply mul_pos hc
    have n1 : 0 ≤ ∑ a ∈ S, (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (Zᵀ - Zᵀᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP1 _
    have n2 : 0 ≤ ∑ a ∈ S', (star (u a) ⬝ᵥ (((-(Complex.I / 2)) • (-Z'ᵀ - (-Z'ᵀ)ᴴ)) *ᵥ u a)).re :=
      Finset.sum_nonneg fun a _ => quad_nonneg hP2 _
    cases hb : epsT t ε a
    · have haS : a ∈ S' := by simp [hS', hb]
      have p2 := Finset.sum_pos' (fun a _ => quad_nonneg hP2 (u a)) ⟨a, haS, quad_pos hP2 ha⟩
      linarith
    · have haS : a ∈ S := by simp [hS, hb]
      have p1 := Finset.sum_pos' (fun a _ => quad_nonneg hP1 (u a)) ⟨a, haS, quad_pos hP1 ha⟩
      linarith
  obtain ⟨κ, hκ, hco⟩ := coercive_of_pos B hpos
  obtain ⟨g, hg, -⟩ := GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form _ B κ hκ hco
  refine ⟨g, ?_⟩
  rw [hgC]
  funext u
  exact hg u

/- English proof (translation)
Introduce `m n ε t c hc htc Z hZ`. Use `show IsSch (gC ε t c Z Zᴴ)`. Conclude with `gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)`.
-/
theorem gZSch : GZSch := by
  intro m n ε t c hc htc Z hZ
  show IsSch (gC ε t c Z Zᴴ)
  exact gCSch m n ε t c hc htc Z Zᴴ hZ (by rw [Matrix.conjTranspose_conjTranspose]; exact hZ)

end PositivityTheory.Rg.Sw.Glob
