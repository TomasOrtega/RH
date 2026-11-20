import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n P hP`. Establish `: P.IsPrime` using `hP.isPrime`. Take `⟨j, hj⟩` from `hP.isRelevant`. Use `set D := MvPolynomial (Fin n) F ⧸ P`. Establish `hr : Ideal.Quotient.mk P (X j) ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hj`. Establish `hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0`. Assume the negation of the conclusion as `hne`. Apply `hr` to reduce the goal to its premises.

Use `h₁ F D _ (fun φ => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hne ⟨φ, h⟩`. Take `⟨φ, hφj⟩` from `hφ`. Establish `hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i)))`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[AlgHom.comp_apply, aeval_X]`. Both sides reduce to the same expression. Use `⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Conclude with `hφj (congrFun h0 j)`. Introduce `g hg`. Rewrite using `[← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]`.
-/
theorem ProjNullstellensatz.proof (h₁ : FGNullstellensatz.Statement) :
    ProjNullstellensatz.Statement := by
  intro F _ n P hP
  have : P.IsPrime := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  set D := MvPolynomial (Fin n) F ⧸ P
  have hr : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  have hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0 := by
    by_contra hne
    apply hr
    refine h₁ F D _ (fun φ => ?_)
    by_contra h
    exact hne ⟨φ, h⟩
  obtain ⟨φ, hφj⟩ := hφ
  have hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩
  · intro h0
    exact hφj (congrFun h0 j)
  · intro g hg
    rw [← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]

end GroundTheory.Heights₂.Heights
