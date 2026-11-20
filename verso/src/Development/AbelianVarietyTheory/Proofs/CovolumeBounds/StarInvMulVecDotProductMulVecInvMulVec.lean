import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.OneLeDetOneAdd

open Matrix
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/- English proof (translation)
Take `⟨C, rfl⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg`. Establish `h` using `(hB.mul_mul_conjTranspose_same C).trace_nonneg`. Rewrite `h` using `[trace_mul_cycle, ← star_eq_conjTranspose]`. Then use the resulting hypothesis.
-/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rwa [trace_mul_cycle, ← star_eq_conjTranspose] at h

/- English proof (translation)
The claim follows from `(RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1`.
-/
theorem re_trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

omit [Fintype n] in
/- English proof (translation)
The claim follows from `(hA.nonneg.trans h).posSemidef`.
-/
theorem posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef :=
  (hA.nonneg.trans h).posSemidef

omit [Fintype n] in
/- English proof (translation)
Use `hA.add_posSemidef (le_iff.mp h)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have := hA.add_posSemidef (le_iff.mp h)
  rwa [add_sub_cancel] at this

/- English proof (translation)
Use `(le_iff.mp h).conjTranspose_mul_mul_same C` as an intermediate fact. Rewrite `this` using `[Matrix.mul_sub, Matrix.sub_mul]`. Then use the resulting hypothesis.
-/
theorem conjTranspose_mul_mul_le_of_le {m : Type*} [Finite m] {A B : Matrix n n 𝕜} (h : A ≤ B)
    (C : Matrix n m 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  have := (le_iff.mp h).conjTranspose_mul_mul_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

omit [Fintype n] in
/- English proof (translation)
Use `(le_iff.mp h).transpose` as an intermediate fact. Rewrite `this` using `[transpose_sub]`. Then use the resulting hypothesis.
-/
theorem transpose_le_transpose_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  have := (le_iff.mp h).transpose
  rwa [transpose_sub] at this

omit [Fintype n] in
/- English proof (translation)
Use `(le_iff.mp h).smul hc` as an intermediate fact. Rewrite `this` using `[smul_sub]`. Then use the resulting hypothesis.
-/
theorem real_smul_le_real_smul_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have := (le_iff.mp h).smul hc
  rwa [smul_sub] at this

variable [DecidableEq n]

/- English proof (translation)
Establish `hB` using `posDef_of_le hA h`. Establish `hAi` using `hA.inv`. Set `_` to `hB.isUnit.invertible`. Set `_` to `hA.isUnit.invertible`. Set `_` to `hAi.isUnit.invertible`.

Establish `h1` using `PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi`. Establish `h2` using `PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB`. Simplify using `only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2`. Conclude with `h2.mp (h1.mpr h)`.
-/
theorem inv_le_inv_of_posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB := posDef_of_le hA h
  have hAi := hA.inv
  let _ := hB.isUnit.invertible
  let _ := hA.isUnit.invertible
  let _ := hAi.isUnit.invertible
  have h1 := PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi
  have h2 := PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2
  exact h2.mp (h1.mpr h)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add`. Consider the case `exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add`. Consider the case `(apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add ..)`.
-/
theorem one_le_det_one_add_of_posSemidef {D : Matrix n n 𝕜} (hD : D.PosSemidef) :
    1 ≤ (1 + D).det := by
  first
  | exact @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | (apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add ..)

/- English proof (translation)
Distinguish the cases in `h0 : A.det = 0`. Rewrite using `[h0]`. Conclude with `(posSemidef_of_le hA h).det_nonneg`. Establish `hA'` using `hA.posDef_iff_det_ne_zero.mpr h0`. Take `⟨C, hC, rfl⟩` from `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hA'.isStrictlyPositive`.

Set `_` to `hC.invertible`. Establish `hD` using `(le_iff.mp h).conjTranspose_mul_mul_same C⁻¹`. Establish `hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C`. Establish `e1 : star C * C⁻¹ᴴ = 1`. Rewrite using `[star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]`. Establish `h1` using `one_le_det_one_add_of_posSemidef hD`. Rewrite using `[hB, det_mul_right_comm, det_mul (star C * C)]`. Conclude with `le_mul_of_one_le_right hA.det_nonneg h1`.
-/
theorem det_le_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) :
    A.det ≤ B.det := by
  by_cases h0 : A.det = 0
  · rw [h0]; exact (posSemidef_of_le hA h).det_nonneg
  have hA' := hA.posDef_iff_det_ne_zero.mpr h0
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA'.isStrictlyPositive
  let _ := hC.invertible
  have hD := (le_iff.mp h).conjTranspose_mul_mul_same C⁻¹
  have hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C := by
    have e1 : star C * C⁻¹ᴴ = 1 := by
      rw [star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1,
      Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]
  have h1 := one_le_det_one_add_of_posSemidef hD
  rw [hB, det_mul_right_comm, det_mul (star C * C)]
  exact le_mul_of_one_le_right hA.det_nonneg h1

/- English proof (translation)
The claim follows from `(RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1`.
-/
theorem re_det_le_re_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det :=
  (RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1

/- English proof (translation)
The claim follows from `(RCLike.pos_iff.mp hA.det_pos).1`.
-/
theorem re_det_pos_of_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det :=
  (RCLike.pos_iff.mp hA.det_pos).1

/- English proof (translation)
Use `re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h` as an intermediate fact. Rewrite `this` using `[RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]`. Then use the resulting hypothesis.
-/
theorem pow_mul_re_det_le_of_smul_le {B B' : Matrix n n 𝕜} (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) (h : c • B ≤ B') :
    c ^ Fintype.card n * RCLike.re B.det ≤ RCLike.re B'.det := by
  have := re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul] at this

/- English proof (translation)
Set `_` to `hB.isUnit.invertible`. Apply `inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, inv_mul_of_invertible]`.
-/
theorem inv_real_smul_of_posDef {B : Matrix n n 𝕜} (hB : B.PosDef) {c : ℝ} (hc : c ≠ 0) :
    (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  let _ := hB.isUnit.invertible
  apply inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
    inv_mul_of_invertible]

/- English proof (translation)
Establish `hU : (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜) = 1` using `Unitary.coe_mul_star_self _`. Establish `h1 : A.trace • (1 : Matrix n n 𝕜) - A = (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (fun i => A.trace - (hA.1.eigenvalues i : 𝕜)) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜)`. Rewrite using `[← diagonal_sub, ← smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]`. Use `congr 1`. Use `conv_lhs => rw [hA.1.spectral_theorem]`.

Both sides reduce to the same expression. Rewrite using `[le_iff, h1]`. Use `PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i => ?_) _` and prove the remaining obligations. Establish `: hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j` using `Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)`. Simplify using `only [Pi.zero_apply, sub_nonneg]`.

Rewrite using `[hA.1.trace_eq_sum_eigenvalues]`. Conclude with `this` after adjusting the coercions.
-/
theorem le_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n 𝕜) := by
  have hU : (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := Unitary.coe_mul_star_self _
  have h1 : A.trace • (1 : Matrix n n 𝕜) - A = (hA.1.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => A.trace - (hA.1.eigenvalues i : 𝕜)) *
        star (hA.1.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [← diagonal_sub, ← smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
    congr 1
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  rw [le_iff, h1]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i => ?_) _
  have : hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  simp only [Pi.zero_apply, sub_nonneg]
  rw [hA.1.trace_eq_sum_eigenvalues]
  exact_mod_cast this

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Rewrite using `[RCLike.real_smul_eq_coe_smul (K := 𝕜)]`. Use `congr 1`. Conclude with `(RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2)).symm`.
-/
theorem smul_eq_re_smul_of_nonneg {c : 𝕜} (hc : 0 ≤ c) (A : Matrix n n 𝕜) :
    c • A = RCLike.re c • A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  congr 1
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2)).symm

/- English proof (translation)
Rewrite using `[← smul_eq_re_smul_of_nonneg hA.trace_nonneg]`. Conclude with `le_trace_smul_one_of_posSemidef hA`.
-/
theorem le_re_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ RCLike.re A.trace • (1 : Matrix n n 𝕜) := by
  rw [← smul_eq_re_smul_of_nonneg hA.trace_nonneg]
  exact le_trace_smul_one_of_posSemidef hA

/- English proof (translation)
Take `⟨C, hC, rfl⟩` from `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hl.isStrictlyPositive`. Set `_` to `hC.invertible`. Establish `h1` using `le_re_trace_smul_one_of_posSemidef (hb.mul_mul_conjTranspose_same C)`. Establish `h2` using `conjTranspose_mul_mul_le_of_le h1 C⁻¹ᴴ`. Establish `e1 : Cᴴ * C⁻¹ᴴ = 1`.

Rewrite using `[← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]`. Rewrite `h2` using `[conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, trace_mul_cycle]`. Rewrite using `[star_eq_conjTranspose, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv]` and apply the resulting hypothesis.
-/
theorem le_re_trace_mul_smul_inv {l b : Matrix n n 𝕜} (hl : l.PosDef) (hb : b.PosSemidef) :
    b ≤ RCLike.re (l * b).trace • l⁻¹ := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hl.isStrictlyPositive
  let _ := hC.invertible
  have h1 := le_re_trace_smul_one_of_posSemidef (hb.mul_mul_conjTranspose_same C)
  have h2 := conjTranspose_mul_mul_le_of_le h1 C⁻¹ᴴ
  have e1 : Cᴴ * C⁻¹ᴴ = 1 := by
    rw [← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
  rw [conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_of_invertible,
    Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, trace_mul_cycle] at h2
  rwa [star_eq_conjTranspose, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv]

omit [Fintype n] [DecidableEq n] in

/- English proof (translation)
Establish `h` using `(hA.submatrix ![i, j]).det_nonneg`. Rewrite `h` using `[det_fin_two]`. Simplify using `only [submatrix_apply, cons_val_zero, cons_val_one, sub_nonneg] at h`. Establish `h2` using `(RCLike.le_iff_re_im.mp h).1`. Establish `hi` using `(RCLike.nonneg_iff.mp (hA.diag_nonneg (i := i))).2`.

Rewrite `h2` using `[← hA.1.apply j i, RCLike.star_def, RCLike.mul_conj, RCLike.mul_re (A i i), hi]`. Normalize the coercions in `at h2`. Simplify using `using h2`.
-/
theorem norm_sq_apply_le_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by
  have h := (hA.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at h
  simp only [submatrix_apply, cons_val_zero, cons_val_one, sub_nonneg] at h
  have h2 := (RCLike.le_iff_re_im.mp h).1
  have hi := (RCLike.nonneg_iff.mp (hA.diag_nonneg (i := i))).2
  rw [← hA.1.apply j i, RCLike.star_def, RCLike.mul_conj, RCLike.mul_re (A i i), hi] at h2
  norm_cast at h2
  simpa using h2

section Gram

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

end Gram

/- English proof (translation)
Use `inv_le_inv_of_posDef_of_le hA h` as an intermediate fact. Rewrite `this` using `[inv_real_smul_of_posDef PosDef.one hc.ne', inv_one]`. Then use the resulting hypothesis.
-/
theorem inv_smul_one_le_inv_of_le_smul_one {A : Matrix n n 𝕜} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) (h : A ≤ c • (1 : Matrix n n 𝕜)) : c⁻¹ • (1 : Matrix n n 𝕜) ≤ A⁻¹ := by
  have := inv_le_inv_of_posDef_of_le hA h
  rwa [inv_real_smul_of_posDef PosDef.one hc.ne', inv_one] at this

end RCLike

section Rational

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

open NumberField IsCMField

variable [NumberField K] [IsCMField K]

end Rational

end GlobalTheory
