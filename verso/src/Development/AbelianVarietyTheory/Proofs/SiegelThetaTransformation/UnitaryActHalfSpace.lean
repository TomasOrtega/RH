import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HAct

section Cplx
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}

/- English proof (translation)
Rewrite `h` using `[Matrix.J, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h`. Take `⟨h1, h2, h3, h4⟩` from `h`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(add_neg_eq_zero.1 h1).symm`.

Rewrite using `[add_neg_eq_iff_eq_add.1 h2]`. Normalize the expressions using the abelian group laws. Rewrite using `[add_neg_eq_iff_eq_add.1 h3]`. Normalize the expressions using the abelian group laws. Conclude with `(add_neg_eq_zero.1 h4).symm`.
-/
theorem blocks (h : (fromBlocks A B C D)ᴴ * Matrix.J (Fin N) ℂ * fromBlocks A B C D =
    Matrix.J (Fin N) ℂ) :
    Aᴴ * C = Cᴴ * A ∧ Aᴴ * D = Cᴴ * B + 1 ∧ Dᴴ * A = Bᴴ * C + 1 ∧ Bᴴ * D = Dᴴ * B := by
  rw [Matrix.J, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (add_neg_eq_zero.1 h1).symm
  · rw [add_neg_eq_iff_eq_add.1 h2]; abel
  · rw [add_neg_eq_iff_eq_add.1 h3]; abel
  · exact (add_neg_eq_zero.1 h4).symm

/- English proof (translation)
Establish `e : (Y * Cᴴ + Dᴴ) * (A * Z + B) - (Y * Aᴴ + Bᴴ) * (C * Z + D) = Y * (Cᴴ * A) * Z + Y * (Cᴴ * B) + (Dᴴ * A) * Z + Dᴴ * B - (Y * (Aᴴ * C) * Z + Y * (Aᴴ * D) + (Bᴴ * C) * Z + Bᴴ * D)` using `by noncomm_ring`. Rewrite using `[e, h1, h2, h3, h4]`. Use `noncomm_ring`.
-/
theorem skew (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (Z Y : Matrix (Fin N) (Fin N) ℂ) :
    (Y * Cᴴ + Dᴴ) * (A * Z + B) - (Y * Aᴴ + Bᴴ) * (C * Z + D) = Z - Y := by
  have e : (Y * Cᴴ + Dᴴ) * (A * Z + B) - (Y * Aᴴ + Bᴴ) * (C * Z + D) =
      Y * (Cᴴ * A) * Z + Y * (Cᴴ * B) + (Dᴴ * A) * Z + Dᴴ * B -
        (Y * (Aᴴ * C) * Z + Y * (Aᴴ * D) + (Bᴴ * C) * Z + Bᴴ * D) := by noncomm_ring
  rw [e, h1, h2, h3, h4]
  noncomm_ring

/- English proof (translation)
Rewrite using `[imH, ← skew h1 h2 h3 h4 Z Zᴴ]`. Simplify using `only [conjTranspose_add, conjTranspose_mul]`.
-/
theorem im_eq (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (Z : Matrix (Fin N) (Fin N) ℂ) :
    (2 * I)⁻¹ • ((C * Z + D)ᴴ * (A * Z + B) - (A * Z + B)ᴴ * (C * Z + D)) = imH Z := by
  rw [imH, ← skew h1 h2 h3 h4 Z Zᴴ]
  simp only [conjTranspose_add, conjTranspose_mul]

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hq⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hp` using `hZ.dotProduct_mulVec_pos hv`. Rewrite `hp` using `[← im_eq h1 h2 h3 h4 Z, smul_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hq, mulVec_zero, sub_zero, dotProduct_smul, dotProduct_mulVec, ← star_mulVec, hq]`. Simplify using `at hp`.
-/
theorem det_ne (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hq⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hp := hZ.dotProduct_mulVec_pos hv
  rw [← im_eq h1 h2 h3 h4 Z, smul_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hq,
    mulVec_zero, sub_zero, dotProduct_smul, dotProduct_mulVec, ← star_mulVec, hq] at hp
  simp at hp

/- English proof (translation)
Rewrite using `[← im_eq h1 h2 h3 h4 Z]`. Generalize the expression as in `A * Z + B = P`. Generalize the expression as in `C * Z + D = Q at hQ ⊢`. Establish `hi : Q⁻¹ * Q = 1` using `nonsing_inv_mul Q (Ne.isUnit hQ)`. Establish `e1 : P * Q⁻¹ * Q = P` using `by rw [Matrix.mul_assoc, hi, Matrix.mul_one]`.

Establish `e2 : Qᴴ * (P * Q⁻¹)ᴴ = Pᴴ` using `by rw [← conjTranspose_mul, e1]`. Rewrite using `[imH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, e2, Matrix.mul_assoc, e1]`.
-/
theorem im_act (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (C * Z + D)ᴴ * imH ((A * Z + B) * (C * Z + D)⁻¹) * (C * Z + D) = imH Z := by
  rw [← im_eq h1 h2 h3 h4 Z]
  generalize A * Z + B = P
  generalize C * Z + D = Q at hQ ⊢
  have hi : Q⁻¹ * Q = 1 := nonsing_inv_mul Q (Ne.isUnit hQ)
  have e1 : P * Q⁻¹ * Q = P := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have e2 : Qᴴ * (P * Q⁻¹)ᴴ = Pᴴ := by rw [← conjTranspose_mul, e1]
  rw [imH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, e2, Matrix.mul_assoc,
    e1]

/- English proof (translation)
Establish `h` using `skew h1 h2 h3 h4 Z Z`. Rewrite `h` using `[sub_self, sub_eq_zero]`. Rewrite using `[← Matrix.mul_assoc, h, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hQ), Matrix.mul_one]`.
-/
theorem den'_act (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (Z * Cᴴ + Dᴴ) * ((A * Z + B) * (C * Z + D)⁻¹) = Z * Aᴴ + Bᴴ := by
  have h := skew h1 h2 h3 h4 Z Z
  rw [sub_self, sub_eq_zero] at h
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hQ), Matrix.mul_one]

/- English proof (translation)
Establish `hd` using `den'_act h1 h2 h3 h4 hQ`. Use `set W := (A * Z + B) * (C * Z + D)⁻¹ with hW`. Establish `e1 : W * (C * Z + D) = A * Z + B`. Rewrite using `[hW, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.mul_one]`. Establish `e2 : (Z * Cᴴ + Dᴴ) * (A - W * C) = 1`.

Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hd]`. Establish `e : (Z * Cᴴ + Dᴴ) * A - (Z * Aᴴ + Bᴴ) * C = Z * (Cᴴ * A) + Dᴴ * A - (Z * (Aᴴ * C) + Bᴴ * C)` using `by noncomm_ring`. Rewrite using `[e, h1, h3]`. Use `noncomm_ring`. Establish `e3 : fromBlocks A B C D * fromBlocks 1 Z 0 1 = fromBlocks 1 W 0 1 * fromBlocks (A - W * C) 0 C (C * Z + D)`.

Rewrite using `[fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[e1]`. Establish `e4` using `congrArg det e3`. Rewrite `e4` using `[det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]`. Simplify using `only [det_one, mul_one, one_mul] at e4`.

Rewrite using `[e4, ← mul_assoc, ← det_mul, e2, det_one, one_mul]`.
-/
theorem det_den' (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (Z * Cᴴ + Dᴴ).det * (fromBlocks A B C D).det = (C * Z + D).det := by
  have hd := den'_act h1 h2 h3 h4 hQ
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have e1 : W * (C * Z + D) = A * Z + B := by
    rw [hW, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.mul_one]
  have e2 : (Z * Cᴴ + Dᴴ) * (A - W * C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hd]
    have e : (Z * Cᴴ + Dᴴ) * A - (Z * Aᴴ + Bᴴ) * C =
      Z * (Cᴴ * A) + Dᴴ * A - (Z * (Aᴴ * C) + Bᴴ * C) := by noncomm_ring
    rw [e, h1, h3]
    noncomm_ring
  have e3 : fromBlocks A B C D * fromBlocks 1 Z 0 1 =
      fromBlocks 1 W 0 1 * fromBlocks (A - W * C) 0 C (C * Z + D) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [e1]
  have e4 := congrArg det e3
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at e4
  simp only [det_one, mul_one, one_mul] at e4
  rw [e4, ← mul_assoc, ← det_mul, e2, det_one, one_mul]

/- English proof (translation)
Establish `hi : Q * Q⁻¹ = 1` using `mul_nonsing_inv Q (Ne.isUnit hQ)`. Establish `e : Y = (Q⁻¹)ᴴ * X * Q⁻¹`. Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Use `hX.conjTranspose_mul_mul_same ?_` and prove the remaining obligations. Conclude with `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det Q).2 (Ne.isUnit hQ)))`.
-/
theorem posDef_of {Q Y X : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.det ≠ 0) (h : Qᴴ * Y * Q = X)
    (hX : X.PosDef) : Y.PosDef := by
  have hi : Q * Q⁻¹ = 1 := mul_nonsing_inv Q (Ne.isUnit hQ)
  have e : Y = (Q⁻¹)ᴴ * X * Q⁻¹ := by
    rw [← h]
    calc Y = (Q * Q⁻¹)ᴴ * Y * (Q * Q⁻¹) := by simp [hi]
      _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  refine hX.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_nonsing_inv_iff).2
    ((Matrix.isUnit_iff_isUnit_det Q).2 (Ne.isUnit hQ)))

/- English proof (translation)
Establish `e : X.det = Y.det * ((‖Q.det‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[← h, det_mul, det_mul, det_conjTranspose]`. Use `push_cast`. Rewrite using `[← Complex.conj_mul', Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_re {Q Y X : Matrix (Fin N) (Fin N) ℂ} (h : Qᴴ * Y * Q = X) :
    Y.det.re * ‖Q.det‖ ^ 2 = X.det.re := by
  have e : X.det = Y.det * ((‖Q.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h, det_mul, det_mul, det_conjTranspose]
    push_cast
    rw [← Complex.conj_mul', Complex.star_def]
    ring
  rw [e, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

end Cplx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
The claim follows from `IsCMField.complexEmbedding_complexConj E τ x`.
-/
theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc, Matrix.mul_apply, mul_comm]`.
-/
theorem ccT_mul {α β δ : Type} [Fintype β] (X : Matrix α β E) (Y : Matrix β δ E) :
    ccT (X * Y) = ccT Y * ccT X := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc]`.
-/
theorem ccT_ccT {α β : Type} (X : Matrix α β E) : ccT (ccT X) = X := by
  ext i j
  simp [ccT, cc]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[ccT, cc]`. Simplify using `[ccT, cc, Matrix.one_apply, h, Ne.symm h]`.
-/
theorem ccT_one {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ccT, cc]
  · simp [ccT, cc, Matrix.one_apply, h, Ne.symm h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, emb_cc]`.
-/
theorem map_ccT {α β : Type} (τ : E →+* ℂ) (X : Matrix α β E) :
    (ccT X).map τ = (X.map τ)ᴴ := by
  ext i j
  simp [ccT, emb_cc]

/- English proof (translation)
Establish `h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E` using `h`. Rewrite using `[Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT γ), h', Matrix.J_squared, neg_neg]`.
-/
theorem left_inv {γ : M2 E N} (h : γ ∈ UU E N) :
    -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) * γ = 1 := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT γ), h',
    Matrix.J_squared, neg_neg]

/- English proof (translation)
Establish `h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E` using `h`. Establish `h2 : ccT γ' * Matrix.J (Fin N) E * γ' = Matrix.J (Fin N) E` using `h'`. Express the relevant statement in the definitionally equal form `ccT (γ' * γ) * Matrix.J (Fin N) E * (γ' * γ) = Matrix.J (Fin N) E`. Rewrite using `[ccT_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem {γ γ' : M2 E N} (h : γ ∈ UU E N) (h' : γ' ∈ UU E N) : γ' * γ ∈ UU E N := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have h2 : ccT γ' * Matrix.J (Fin N) E * γ' = Matrix.J (Fin N) E := h'
  change ccT (γ' * γ) * Matrix.J (Fin N) E * (γ' * γ) = Matrix.J (Fin N) E
  rw [ccT_mul]
  calc _ = ccT γ * (ccT γ' * Matrix.J (Fin N) E * γ') * γ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, h1]

/- English proof (translation)
Establish `h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E` using `h`. Establish `hl` using `left_inv h`. Establish `hu : IsUnit γ.det` using `Matrix.isUnit_det_of_left_inverse hl`. Establish `hi : γ * γ⁻¹ = 1` using `mul_nonsing_inv γ hu`. Use `⟨hu, ?_, ?_, Matrix.inv_eq_left_inv hl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ccT γ⁻¹ * Matrix.J (Fin N) E * γ⁻¹ = Matrix.J (Fin N) E`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ccT_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [hi, ccT_one, Matrix.one_mul, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E`.

Rewrite using `[ccT_ccT]`. Establish `hr : γ * -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) = 1` using `mul_eq_one_comm.1 hl`. Establish `h2` using `congrArg (· * Matrix.J (Fin N) E) hr`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_one, neg_neg, Matrix.one_mul] at h2`. Rewrite using `[Matrix.mul_assoc, h2]`.
-/
theorem group_part {γ : M2 E N} (h : γ ∈ UU E N) :
    IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧
      γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have hl := left_inv h
  have hu : IsUnit γ.det := Matrix.isUnit_det_of_left_inverse hl
  have hi : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hu
  refine ⟨hu, ?_, ?_, Matrix.inv_eq_left_inv hl⟩
  · change ccT γ⁻¹ * Matrix.J (Fin N) E * γ⁻¹ = Matrix.J (Fin N) E
    calc _ = ccT γ⁻¹ * (ccT γ * Matrix.J (Fin N) E * γ) * γ⁻¹ := by rw [h1]
      _ = ccT (γ * γ⁻¹) * Matrix.J (Fin N) E * (γ * γ⁻¹) := by
        simp only [ccT_mul, Matrix.mul_assoc]
      _ = _ := by rw [hi, ccT_one, Matrix.one_mul, Matrix.mul_one]
  · change ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E
    rw [ccT_ccT]
    have hr : γ * -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) = 1 := mul_eq_one_comm.1 hl
    have h2 := congrArg (· * Matrix.J (Fin N) E) hr
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_one,
      neg_neg, Matrix.one_mul] at h2
    rw [Matrix.mul_assoc, h2]

/- English proof (translation)
Rewrite using `[← fromBlocks_map, fromBlocks_toBlocks]`.
-/
theorem map_blocks (τ : E →+* ℂ) (γ : M2 E N) :
    γ.map τ = fromBlocks (γ.toBlocks₁₁.map τ) (γ.toBlocks₁₂.map τ) (γ.toBlocks₂₁.map τ)
      (γ.toBlocks₂₂.map τ) := by
  rw [← fromBlocks_map, fromBlocks_toBlocks]

/- English proof (translation)
Establish `h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E` using `h`. Establish `hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>`. Simplify using `[Matrix.J, Matrix.one_apply, hij]`.

Establish `h2` using `congrArg (fun X => X.map τ) h1`. Simplify using `only [Matrix.map_mul, map_ccT, hJ] at h2`. Conclude with `h2`.
-/
theorem map_mem (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>
      simp [Matrix.J, Matrix.one_apply, hij]
  have h2 := congrArg (fun X => X.map τ) h1
  simp only [Matrix.map_mul, map_ccT, hJ] at h2
  exact h2

/- English proof (translation)
Establish `h2` using `congrArg det (map_mem τ h)`. Establish `hJ : (Matrix.J (Fin N) ℂ).det ≠ 0` using `(Matrix.isUnit_det_J (Fin N) ℂ).ne_zero`. Establish `hd : (γ.map τ).det = τ γ.det` using `(RingHom.map_det τ γ).symm`. Rewrite `h2` using `[det_mul, det_mul, det_conjTranspose, hd]`. Establish `h3 : conj (τ γ.det) * τ γ.det = 1`.

Apply `mul_left_cancel₀ hJ` to reduce the goal to its premises. Rewrite `h2` using `[Complex.star_def]`. Take the linear combination `h2`. Establish `h4` using `congrArg norm h3`. Rewrite `h4` using `[norm_mul, Complex.norm_conj, norm_one]`.

Use polynomial arithmetic with `[norm_nonneg (τ γ.det)]`.
-/
theorem norm_det (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) : ‖τ γ.det‖ = 1 := by
  have h2 := congrArg det (map_mem τ h)
  have hJ : (Matrix.J (Fin N) ℂ).det ≠ 0 := (Matrix.isUnit_det_J (Fin N) ℂ).ne_zero
  have hd : (γ.map τ).det = τ γ.det := (RingHom.map_det τ γ).symm
  rw [det_mul, det_mul, det_conjTranspose, hd] at h2
  have h3 : conj (τ γ.det) * τ γ.det = 1 := by
    apply mul_left_cancel₀ hJ
    rw [Complex.star_def] at h2
    linear_combination h2
  have h4 := congrArg norm h3
  rw [norm_mul, Complex.norm_conj, norm_one] at h4
  nlinarith [norm_nonneg (τ γ.det)]

/- English proof (translation)
Establish `h : (γ' * γ).map τ = γ'.map τ * γ.map τ` using `Matrix.map_mul`. Rewrite `h` using `[map_blocks, map_blocks τ γ, map_blocks τ γ', fromBlocks_multiply, fromBlocks_inj]`. Conclude with `h`.
-/
theorem mul_blocks (τ : E →+* ℂ) (γ γ' : M2 E N) :
    (γ' * γ).toBlocks₁₁.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₁₂.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₂.map τ ∧
    (γ' * γ).toBlocks₂₁.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₂₂.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₂.map τ := by
  have h : (γ' * γ).map τ = γ'.map τ * γ.map τ := Matrix.map_mul
  rw [map_blocks, map_blocks τ γ, map_blocks τ γ', fromBlocks_multiply, fromBlocks_inj] at h
  exact h

end GlobalTheory.SW.HAct

open GlobalTheory.SW.HAct in

/- English proof (translation)
Introduce `E _ _ _ Ψ N γ h`. Take `⟨g1, g2, g3, g4⟩` from `group_part h`. Use `⟨⟨g1, g2, g3, g4, fun γ' h' => mul_mem h h'⟩, fun Z hZ => ?_⟩` and prove the remaining obligations. Establish `hb` using `fun τ : Ψ => blocks (map_blocks τ.1 γ ▸ map_mem τ.1 h)`. Establish `hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0` using `fun τ => det_ne (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hZ τ)`.

Establish `hI : ∀ τ, (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)` using `fun τ => im_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)`. Use `⟨fun τ => ⟨hQ τ, ?_, norm_det τ.1 h, hI τ⟩, fun τ => posDef_of (hQ τ) (hI τ) (hZ τ), ?_, fun γ' h' => ?_⟩` and prove the remaining obligations. Use `det_den' (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)` as an intermediate fact. Rewrite `this` using `[← map_blocks τ.1 γ]`. Rewrite using `[RingHom.map_det]`.

Conclude with `this`. Rewrite using `[detIm, detIm, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun τ _ => det_re (hI τ)`. Establish `hW : ∀ τ, hAct Ψ γ Z τ * hDen Ψ γ Z τ = γ.toBlocks₁₁.map τ.1 * Z τ + γ.toBlocks₁₂.map τ.1` using `fun τ => by`. Rewrite using `[hAct, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit (hQ τ)), Matrix.mul_one]`.

Establish `key : ∀ (τ : Ψ) (X Y : Matrix (Fin N) (Fin N) ℂ), (X * γ.toBlocks₁₁.map τ.1 + Y * γ.toBlocks₂₁.map τ.1) * Z τ + (X * γ.toBlocks₁₂.map τ.1 + Y * γ.toBlocks₂₂.map τ.1) = (X * hAct Ψ γ Z τ + Y) * hDen Ψ γ Z τ` using `fun τ X Y => by`. Rewrite using `[Matrix.add_mul (X * hAct Ψ γ Z τ), Matrix.mul_assoc, hW, hDen]`. Use `noncomm_ring`. Establish `hD : ∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ` using `fun τ => by`. Take `⟨-, -, m3, m4⟩` from `mul_blocks τ.1 γ γ'`.

Rewrite using `[hDen, m3, m4, key]`. Both sides reduce to the same expression. Use `⟨funext fun τ => ?_, hD, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨m1, m2, -, -⟩` from `mul_blocks τ.1 γ γ'`. Rewrite using `[hAct, hD, m1, m2, key, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (hDen Ψ γ Z τ), mul_nonsing_inv _ (Ne.isUnit (hQ τ)), Matrix.one_mul]`.

Both sides reduce to the same expression. Take `⟨-, -, m3, m4⟩` from `mul_blocks τ.1 γ γ'`. Establish `hd : hDen' Ψ γ Z τ * hAct Ψ γ Z τ = _` using `den'_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)`. Rewrite using `[hDen', m3, m4, hDen', hDen', Matrix.mul_add (_ + _), ← Matrix.mul_assoc (_ + _)]`. Rewrite `hd` using `[hDen']`.

Rewrite using `[hd]`. Simplify using `only [conjTranspose_add, conjTranspose_mul]`. Use `noncomm_ring`.
-/
theorem GlobalTheory.SW.unitary_act_halfSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (N : ℕ) (γ : M2 E N), γ ∈ UU E N → (IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧ γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) ∧ ∀ γ' ∈ UU E N, γ' * γ ∈ UU E N) ∧ ∀ Z ∈ Hn Ψ N, (∀ τ, (hDen Ψ γ Z τ).det ≠ 0 ∧ (hDen' Ψ γ Z τ).det * τ.1 γ.det = (hDen Ψ γ Z τ).det ∧ ‖τ.1 γ.det‖ = 1 ∧ (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)) ∧ hAct Ψ γ Z ∈ Hn Ψ N ∧ detIm (hAct Ψ γ Z) * ∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2 = detIm Z ∧ ∀ γ' ∈ UU E N, hAct Ψ (γ' * γ) Z = hAct Ψ γ' (hAct Ψ γ Z) ∧ (∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ) ∧ ∀ τ, hDen' Ψ (γ' * γ) Z τ = hDen' Ψ γ Z τ * hDen' Ψ γ' (hAct Ψ γ Z) τ := by
  intro E _ _ _ Ψ N γ h
  obtain ⟨g1, g2, g3, g4⟩ := group_part h
  refine ⟨⟨g1, g2, g3, g4, fun γ' h' => mul_mem h h'⟩, fun Z hZ => ?_⟩
  have hb := fun τ : Ψ => blocks (map_blocks τ.1 γ ▸ map_mem τ.1 h)
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ =>
    det_ne (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hZ τ)
  have hI : ∀ τ, (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ) := fun τ =>
    im_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
  refine ⟨fun τ => ⟨hQ τ, ?_, norm_det τ.1 h, hI τ⟩, fun τ => posDef_of (hQ τ) (hI τ) (hZ τ), ?_,
    fun γ' h' => ?_⟩
  · have := det_den' (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
    rw [← map_blocks τ.1 γ] at this
    rw [RingHom.map_det]
    exact this
  · rw [detIm, detIm, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => det_re (hI τ)
  · have hW : ∀ τ, hAct Ψ γ Z τ * hDen Ψ γ Z τ =
        γ.toBlocks₁₁.map τ.1 * Z τ + γ.toBlocks₁₂.map τ.1 := fun τ => by
      rw [hAct, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit (hQ τ)), Matrix.mul_one]
    have key : ∀ (τ : Ψ) (X Y : Matrix (Fin N) (Fin N) ℂ),
        (X * γ.toBlocks₁₁.map τ.1 + Y * γ.toBlocks₂₁.map τ.1) * Z τ +
          (X * γ.toBlocks₁₂.map τ.1 + Y * γ.toBlocks₂₂.map τ.1) =
        (X * hAct Ψ γ Z τ + Y) * hDen Ψ γ Z τ := fun τ X Y => by
      rw [Matrix.add_mul (X * hAct Ψ γ Z τ), Matrix.mul_assoc, hW, hDen]
      noncomm_ring
    have hD : ∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ := fun τ => by
      obtain ⟨-, -, m3, m4⟩ := mul_blocks τ.1 γ γ'
      rw [hDen, m3, m4, key]
      rfl
    refine ⟨funext fun τ => ?_, hD, fun τ => ?_⟩
    · obtain ⟨m1, m2, -, -⟩ := mul_blocks τ.1 γ γ'
      rw [hAct, hD, m1, m2, key, Matrix.mul_inv_rev, Matrix.mul_assoc,
        ← Matrix.mul_assoc (hDen Ψ γ Z τ), mul_nonsing_inv _ (Ne.isUnit (hQ τ)), Matrix.one_mul]
      rfl
    · obtain ⟨-, -, m3, m4⟩ := mul_blocks τ.1 γ γ'
      have hd : hDen' Ψ γ Z τ * hAct Ψ γ Z τ = _ :=
        den'_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
      rw [hDen', m3, m4, hDen', hDen', Matrix.mul_add (_ + _), ← Matrix.mul_assoc (_ + _)]
      rw [hDen'] at hd
      rw [hd]
      simp only [conjTranspose_add, conjTranspose_mul]
      noncomm_ring
