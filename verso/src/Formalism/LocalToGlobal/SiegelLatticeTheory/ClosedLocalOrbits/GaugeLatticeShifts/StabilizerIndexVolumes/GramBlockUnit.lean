import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Unfold `Formalism.MainNotions.S.leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`.
-/
theorem leadMinor_top {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.MainNotions.S.leadMinorE Z (r + 1) = Z.det := by
  unfold Formalism.MainNotions.S.leadMinorE
  rw [dif_pos le_rfl]
  congr 1

/- English proof (translation)
Unfold `Formalism.MainNotions.S.leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ r), Matrix.adjugate_fin_succ_eq_det_submatrix]`. Establish `: (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1`. Rewrite using `[← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[this, one_mul, Fin.succAbove_last]`. Both sides reduce to the same expression.
-/
theorem leadMinor_r {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.MainNotions.S.leadMinorE Z r = Z.adjugate (Fin.last r) (Fin.last r) := by
  unfold Formalism.MainNotions.S.leadMinorE
  rw [dif_pos (Nat.le_succ r), Matrix.adjugate_fin_succ_eq_det_submatrix]
  have : (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul, Fin.succAbove_last]
  rfl

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Use `set l := Fin.last r`. Use `set α : Fin (r + 1) → E := fun a => v (Sum.inl a)`.

Use `set β : Fin (r + 1) → E := fun b => v (Sum.inr b)`. Establish `hJ : ∀ (c : E) (γ : Fin (r + 1) → E) (a : Fin (r + 1)), ∑ b, (if a = l ∧ b = l then c else 0) * γ b = if a = l then c * γ l else 0`. Introduce `c γ a`. Distinguish the cases in `ha : a = l`. Simplify using `[ha]`.

Simplify using `[ha]`. Establish `E1 : Z *ᵥ β = Pi.single l (T * α l)`. Use extensionality with `a`. Use `congrFun hv (Sum.inl a)` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h11, h12, Pi.zero_apply] at this`.

Rewrite `this` using `[hJ]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply]`. Distinguish the cases in `ha : a = l`. Rewrite `this`, the goal using `[if_pos ha]`. Take the linear combination `this`.

Rewrite `this`, the goal using `[if_neg ha]`. Take the linear combination `this`. Establish `E2 : Z.conjTranspose *ᵥ α = Pi.single l (T' * β l)`. Use extensionality with `a`. Use `congrFun hv (Sum.inr a)` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h21, h22, Pi.zero_apply] at this`. Rewrite `this` using `[hJ]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.conjTranspose_apply]`. Distinguish the cases in `ha : a = l`. Rewrite `this`, the goal using `[if_pos ha]`.

Take the linear combination `this`. Rewrite `this`, the goal using `[if_neg ha]`. Take the linear combination `this`. Establish `hZi : Z⁻¹ * Z = 1` using `nonsing_inv_mul _ hZ`. Establish `hZti : IsUnit Z.conjTranspose.det`.

Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `hZ.star`. Establish `Eβ : β = Z⁻¹ *ᵥ Pi.single l (T * α l)`. Rewrite using `[← E1, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]`. Establish `Eα : α = (Z.conjTranspose)⁻¹ *ᵥ Pi.single l (T' * β l)`.

Rewrite using `[← E2, Matrix.mulVec_mulVec, nonsing_inv_mul _ hZti, Matrix.one_mulVec]`. Use `set ζ := Z⁻¹ l l`. Establish `hβl : β l = ζ * (T * α l)`. Use `congrFun Eβ l` as an intermediate fact. Rewrite using `[this, Matrix.mulVec_single]`.

Simplify using `[ζ]`. Establish `hαl : α l = star ζ * (T' * β l)`. Use `congrFun Eα l` as an intermediate fact. Rewrite using `[this, Matrix.mulVec_single, ← Matrix.conjTranspose_nonsing_inv]`. Simplify using `[ζ, Matrix.conjTranspose_apply]`.

Establish `hD : Z.det ≠ 0` using `hZ.ne_zero`. Establish `hζ : ζ * Z.det = Formalism.MainNotions.S.leadMinorE Z r`. Rewrite using `[leadMinor_r, show ζ = Z⁻¹ l l from rfl, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.

Establish `hαG : α l * (Formalism.MainNotions.S.leadMinorE Z (r + 1) * star (Formalism.MainNotions.S.leadMinorE Z (r + 1)) - T * T' * (Formalism.MainNotions.S.leadMinorE Z r * star (Formalism.MainNotions.S.leadMinorE Z r))) = 0`. Rewrite using `[leadMinor_top, ← hζ, star_mul']`. Establish `h3 : α l = star ζ * T' * ζ * T * α l`. Combine the equalities or inequalities in the displayed calculation. Take the linear combination `(Z.det * star Z.det) * h3`.

Establish `hαl0 : α l = 0`. Break down `mul_eq_zero.mp hαG with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hG`. Establish `hβ0 : β = 0` using `by rw [Eβ, hαl0]; simp`.

Establish `hα0 : α = 0` using `by rw [Eα, show β l = 0 from by rw [hβ0]; rfl]; simp`. Apply `hv0` to reduce the goal to its premises. Use extensionality with `x`. Break down `x with a | b` into its components or cases. Conclude with `congrFun hα0 a`.

Conclude with `congrFun hβ0 b`.
-/
theorem gram_block_unit {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (hTs : star T = T)
    (hT's : star T' = T') (hZ : IsUnit Z.det)
    (hG : Formalism.MainNotions.S.leadMinorE Z (r + 1) * star (Formalism.MainNotions.S.leadMinorE Z (r + 1)) -
      T * T' * (Formalism.MainNotions.S.leadMinorE Z r * star (Formalism.MainNotions.S.leadMinorE Z r)) ≠ 0)
    (Gr : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E)
    (h11 : ∀ a b, Gr (Sum.inl a) (Sum.inl b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (h12 : ∀ a b, Gr (Sum.inl a) (Sum.inr b) = Z a b)
    (h21 : ∀ a b, Gr (Sum.inr a) (Sum.inl b) = star (Z b a))
    (h22 : ∀ a b, Gr (Sum.inr a) (Sum.inr b) = if a = Fin.last r ∧ b = Fin.last r then -T' else 0) :
    IsUnit Gr.det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set l := Fin.last r
  set α : Fin (r + 1) → E := fun a => v (Sum.inl a)
  set β : Fin (r + 1) → E := fun b => v (Sum.inr b)
  have hJ : ∀ (c : E) (γ : Fin (r + 1) → E) (a : Fin (r + 1)),
      ∑ b, (if a = l ∧ b = l then c else 0) * γ b = if a = l then c * γ l else 0 := by
    intro c γ a
    by_cases ha : a = l
    · simp [ha]
    · simp [ha]
  have E1 : Z *ᵥ β = Pi.single l (T * α l) := by
    ext a
    have := congrFun hv (Sum.inl a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h11, h12, Pi.zero_apply] at this
    rw [hJ] at this
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    by_cases ha : a = l
    · rw [if_pos ha] at this ⊢; linear_combination this
    · rw [if_neg ha] at this ⊢; linear_combination this
  have E2 : Z.conjTranspose *ᵥ α = Pi.single l (T' * β l) := by
    ext a
    have := congrFun hv (Sum.inr a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h21, h22, Pi.zero_apply] at this
    rw [hJ] at this
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.conjTranspose_apply]
    by_cases ha : a = l
    · rw [if_pos ha] at this ⊢; linear_combination this
    · rw [if_neg ha] at this ⊢; linear_combination this
  have hZi : Z⁻¹ * Z = 1 := nonsing_inv_mul _ hZ
  have hZti : IsUnit Z.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]; exact hZ.star
  have Eβ : β = Z⁻¹ *ᵥ Pi.single l (T * α l) := by
    rw [← E1, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have Eα : α = (Z.conjTranspose)⁻¹ *ᵥ Pi.single l (T' * β l) := by
    rw [← E2, Matrix.mulVec_mulVec, nonsing_inv_mul _ hZti, Matrix.one_mulVec]
  set ζ := Z⁻¹ l l
  have hβl : β l = ζ * (T * α l) := by
    have := congrFun Eβ l
    rw [this, Matrix.mulVec_single]; simp [ζ]
  have hαl : α l = star ζ * (T' * β l) := by
    have := congrFun Eα l
    rw [this, Matrix.mulVec_single, ← Matrix.conjTranspose_nonsing_inv]; simp [ζ, Matrix.conjTranspose_apply]
  have hD : Z.det ≠ 0 := hZ.ne_zero
  have hζ : ζ * Z.det = Formalism.MainNotions.S.leadMinorE Z r := by
    rw [leadMinor_r, show ζ = Z⁻¹ l l from rfl, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv',
      smul_eq_mul]
    field_simp
    rfl
  have hαG : α l * (Formalism.MainNotions.S.leadMinorE Z (r + 1) * star (Formalism.MainNotions.S.leadMinorE Z (r + 1)) -
      T * T' * (Formalism.MainNotions.S.leadMinorE Z r * star (Formalism.MainNotions.S.leadMinorE Z r))) = 0 := by
    rw [leadMinor_top, ← hζ, star_mul']
    have h3 : α l = star ζ * T' * ζ * T * α l := by
      calc α l = star ζ * (T' * β l) := hαl
        _ = star ζ * (T' * (ζ * (T * α l))) := by rw [hβl]
        _ = star ζ * T' * ζ * T * α l := by ring
    linear_combination (Z.det * star Z.det) * h3
  have hαl0 : α l = 0 := by
    rcases mul_eq_zero.mp hαG with h | h
    · exact h
    · exact absurd h hG
  have hβ0 : β = 0 := by rw [Eβ, hαl0]; simp
  have hα0 : α = 0 := by rw [Eα, show β l = 0 from by rw [hβ0]; rfl]; simp
  apply hv0
  ext x
  rcases x with a | b
  · exact congrFun hα0 a
  · exact congrFun hβ0 b

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
