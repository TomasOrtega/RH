import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin.Holo

open Matrix
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `fun_prop`.
-/
theorem differentiable_det {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : Type*} [Fintype n]
    [DecidableEq n] (f : F → Matrix n n ℂ) (hf : ∀ i j, Differentiable ℂ fun x => f x i j) :
    Differentiable ℂ fun x => (f x).det := by
  simp only [Matrix.det_apply']
  fun_prop

/- English proof (translation)
Introduce `hdet`. Use `set A := m.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA`. Establish `hdc : (A.map (starRingEnd ℂ)).det = 0`. Rewrite using `[show A.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix A from rfl, ← RingHom.map_det, hdet, map_zero]`. Take `⟨v, hv, hAv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdc`.

Establish `h` using `hpos.dotProduct_mulVec_pos hv`. Use `set u : Fin r → ℂ := fun k => ∑ b, starRingEnd ℂ (m k (Fin.castLE hp b)) * v b with hu_def`. Establish `hu : ∀ i : Fin p, u (Fin.castLE hp i) = 0` using `fun i => by`. Use `congrFun hAv i` as an intermediate fact. Simplify `this` using `[hA, Matrix.mulVec, dotProduct, u]`.

Establish `hq : star v ⬝ᵥ ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp) *ᵥ v) = ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k)`. Simplify using `only [dotProduct, mulVec, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hu_def, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_m …`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_lhs => arg 2`. Use extensionality with `b`.

Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hq' : ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) = ((∑ k : Fin r, sgn p (k : ℕ) * Complex.normSq (u k) : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Rewrite `h` using `[hq, hq', Complex.zero_lt_real]`.

Use `absurd h (not_lt.2 (Finset.sum_nonpos fun k _ => ?_))` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < p`. Establish `h0 : u k = 0`. Use `hu ⟨k, hk⟩` as an intermediate fact. Rewrite `this` using `[show Fin.castLE hp ⟨k, hk⟩ = k from Fin.ext rfl]`. Then use the resulting hypothesis.

Simplify using `[h0]`. Simplify using `only [sgn, if_neg hk]`. Use polynomial arithmetic with `[Complex.normSq_nonneg (u k)]`.
-/
theorem det_block_ne {r p : ℕ} (hp : p ≤ r) (m : Matrix (Fin r) (Fin r) ℂ)
    (hpos : ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp)).PosDef) :
    (m.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro hdet
  set A := m.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hdc : (A.map (starRingEnd ℂ)).det = 0 := by
    rw [show A.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix A from rfl, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdc
  have h := hpos.dotProduct_mulVec_pos hv
  set u : Fin r → ℂ := fun k => ∑ b, starRingEnd ℂ (m k (Fin.castLE hp b)) * v b with hu_def
  have hu : ∀ i : Fin p, u (Fin.castLE hp i) = 0 := fun i => by
    have := congrFun hAv i
    simpa [hA, Matrix.mulVec, dotProduct, u] using this
  have hq : star v ⬝ᵥ ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp) *ᵥ v) =
      ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) := by
    simp only [dotProduct, mulVec, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, hu_def, map_sum, map_mul, Complex.conj_conj,
      Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]
    ring
  have hq' : ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) =
      ((∑ k : Fin r, sgn p (k : ℕ) * Complex.normSq (u k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hq, hq', Complex.zero_lt_real] at h
  refine absurd h (not_lt.2 (Finset.sum_nonpos fun k _ => ?_))
  by_cases hk : (k : ℕ) < p
  · have h0 : u k = 0 := by
      have := hu ⟨k, hk⟩
      rwa [show Fin.castLE hp ⟨k, hk⟩ = k from Fin.ext rfl] at this
    simp [h0]
  · simp only [sgn, if_neg hk]
    nlinarith [Complex.normSq_nonneg (u k)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `h0` using `ExF.det_ne_of_orth X ho τ`. Use `set m := (mat x0 τ)⁻¹ * mat x τ with hm`. Establish `hxm : mat x τ = mat x0 τ * m`. Rewrite using `[hm, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 h0)]`. Establish `hg : gram τ.1 X.Gm (mat x τ) = mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * m.map (starRingEnd ℂ)`.

Rewrite using `[hxm, FrameDegreeData.gram_mul, ho τ]`. Establish `hpos` using `X.gramPos_posDef hx τ`. Rewrite `hpos` using `[Data.gramPos, hg]`. Establish `hb : (KU.Mx X x0 x τ).toBlocks₂₂ = m.submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)`. Use extensionality with `i j`.

Simplify using `[KU.Mx, KU.tl, Matrix.toBlocks₂₂, KU.eT_inr, m]`. Rewrite using `[hb]`. Conclude with `det_block_ne X.p0_le m hpos`.
-/
theorem det_Mx₂₂_ne (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) : (KU.Mx X x0 x τ).toBlocks₂₂.det ≠ 0 := by
  have h0 := ExF.det_ne_of_orth X ho τ
  set m := (mat x0 τ)⁻¹ * mat x τ with hm
  have hxm : mat x τ = mat x0 τ * m := by
    rw [hm, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 h0)]
  have hg : gram τ.1 X.Gm (mat x τ) = mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ) := by
    rw [hxm, FrameDegreeData.gram_mul, ho τ]
  have hpos := X.gramPos_posDef hx τ
  rw [Data.gramPos, hg] at hpos
  have hb : (KU.Mx X x0 x τ).toBlocks₂₂ = m.submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
    ext i j
    simp [KU.Mx, KU.tl, Matrix.toBlocks₂₂, KU.eT_inr, m]
  rw [hb]
  exact det_block_ne X.p0_le m hpos

/- English proof (translation)
Simplify using `only [KU.Mx, KU.tl, Matrix.submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem differentiable_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i j) :
    Differentiable ℂ fun x : Frame X.Ψ r => KU.Mx X x0 x τ i j := by
  simp only [KU.Mx, KU.tl, Matrix.submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Establish `hd1 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).det` using `fun τ => differentiable_det _ (differentiable_Mx X x0 τ)`. Establish `hd2 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det` using `fun τ => differentiable_det (fun x => (KU.Mx X x0 x τ).toBlocks₂₂) fun i j => differentiable_Mx X x0 τ (Sum.inr i) (Sum.inr j)`. Establish `hq : qS X x0 k = ∏ τ, fun x : Frame X.Ψ r => ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k`. Use function extensionality and compare the values at `x`. Simplify using `[qS, Finset.prod_apply]`.

Rewrite using `[hq]`. Use `Finset.prod_induction _ (fun g : Frame X.Ψ r → ℂ => DifferentiableOn ℂ g X.dom) (fun a b ha hb => ha.mul hb) (differentiableOn_const 1) fun τ _ => ?_` and prove the remaining obligations. Establish `hne : ∀ x ∈ X.dom, (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2 ≠ 0` using `fun x hx => pow_ne_zero 2 (det_Mx₂₂_ne X ho hx τ)`. Establish `h1` using `(hd1 τ).differentiableOn (s := X.dom)`. Establish `h2 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom` using `((hd2 τ).differentiableOn).pow 2`.

Establish `h3 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom`. Use `by`. Simplify using `only [div_eq_mul_inv]`. Conclude with `h1.mul (h2.inv hne)`. Conclude with `h3.pow k`.
-/
theorem qS_differentiableOn (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (k : ℕ) :
    DifferentiableOn ℂ (qS X x0 k) X.dom := by
  have hd1 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).det := fun τ =>
    differentiable_det _ (differentiable_Mx X x0 τ)
  have hd2 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det := fun τ =>
    differentiable_det (fun x => (KU.Mx X x0 x τ).toBlocks₂₂) fun i j =>
      differentiable_Mx X x0 τ (Sum.inr i) (Sum.inr j)
  have hq : qS X x0 k = ∏ τ, fun x : Frame X.Ψ r =>
      ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k := by
    funext x
    simp [qS, Finset.prod_apply]
  rw [hq]
  refine Finset.prod_induction _ (fun g : Frame X.Ψ r → ℂ => DifferentiableOn ℂ g X.dom)
    (fun a b ha hb => ha.mul hb) (differentiableOn_const 1) fun τ _ => ?_
  have hne : ∀ x ∈ X.dom, (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (det_Mx₂₂_ne X ho hx τ)
  have h1 := (hd1 τ).differentiableOn (s := X.dom)
  have h2 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
    ((hd2 τ).differentiableOn).pow 2
  have h3 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
by
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv hne)
  exact h3.pow k

/- English proof (translation)
Introduce `_ _ _ _ _ X x0 ho k` and use `qS_differentiableOn X x0 ho k`.
-/
theorem qS_holomorphicOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r),
    IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom :=
  fun _ _ _ _ _ X x0 ho k => qS_differentiableOn X x0 ho k

end

end GlobalTheory.ScalarPoin.Holo
