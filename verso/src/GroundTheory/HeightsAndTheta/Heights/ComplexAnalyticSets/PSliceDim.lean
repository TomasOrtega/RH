import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[homogeneousComponent_zero]`. Simplify using `[linForm, coeff_sum, coeff_C_mul, coeff_X]`.
-/
theorem SliceDim.homogeneousComponent_zero_linForm_sub_one {n : ℕ} (ℓ : Fin n → ℂ) :
    homogeneousComponent 0 (linForm ℓ - 1 : MvPolynomial (Fin n) ℂ) = -1 := by
  rw [homogeneousComponent_zero]
  simp [linForm, coeff_sum, coeff_C_mul, coeff_X]

/- English proof (translation)
Introduce `h`. Establish `h0` using `hH _ h 0`. Rewrite `h0` using `[SliceDim.homogeneousComponent_zero_linForm_sub_one, neg_mem_iff]`. Conclude with `hJ ((Ideal.eq_top_iff_one J).mpr h0)`.
-/
theorem SliceDim.linForm_sub_one_not_mem {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hH : IsHomogIdeal J) (hJ : J ≠ ⊤) (ℓ : Fin n → ℂ) : linForm ℓ - 1 ∉ J := by
  intro h
  have h0 := hH _ h 0
  rw [SliceDim.homogeneousComponent_zero_linForm_sub_one, neg_mem_iff] at h0
  exact hJ ((Ideal.eq_top_iff_one J).mpr h0)

/- English proof (translation)
Introduce `n e J ℓ hJ hdim hℓ`. Establish `hP` using `hJ.isPrime`. Use `le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice ⟨hP, hdim⟩ hJ.isHomog hℓ)` and prove the remaining obligations. Use `set r := Ideal.Quotient.mk J (linForm ℓ - 1) with hr_def`. Establish `hr0 : r ≠ 0`.

Rewrite using `[hr_def, Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `SliceDim.linForm_sub_one_not_mem hJ.isHomog hP.ne_top ℓ`. Establish `hr : r ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J)` using `mem_nonZeroDivisors_of_ne_zero hr0`. Establish `hle : J ≤ J ⊔ Ideal.span {linForm ℓ - 1}` using `le_sup_left`. Establish `hkill : Ideal.Quotient.factor hle r = 0`.

Rewrite using `[hr_def, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `le_sup_right (a := J) (Ideal.subset_span rfl)`. Establish `key` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle) hr hkill`. Rewrite `key` using `[hdim]`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at key ⊢`.

Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe b`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Normalize the coercions in `at key`. Consider the case `coe m`. Establish `: m + 1 ≤ e + 1` using `by exact_mod_cast key`. Conclude with `(by omega : m ≤ e)` after adjusting the coercions.
-/
theorem SliceDim.proof : SliceDim.Statement := by
  intro n e J ℓ hJ hdim hℓ
  have hP := hJ.isPrime
  refine le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice ⟨hP, hdim⟩ hJ.isHomog hℓ)
  set r := Ideal.Quotient.mk J (linForm ℓ - 1) with hr_def
  have hr0 : r ≠ 0 := by
    rw [hr_def, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact SliceDim.linForm_sub_one_not_mem hJ.isHomog hP.ne_top ℓ
  have hr : r ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle : J ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_left
  have hkill : Ideal.Quotient.factor hle r = 0 := by
    rw [hr_def, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact le_sup_right (a := J) (Ideal.subset_span rfl)
  have key := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr hkill
  rw [hdim] at key
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      norm_cast at key
    | coe m =>
      have : m + 1 ≤ e + 1 := by exact_mod_cast key
      exact_mod_cast (by omega : m ≤ e)

end

end GroundTheory.Heights₂.Heights
