import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem exists_rightInv_of_span {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  refine GlobalTheory.ZeroCycleHt.exists_rightInv fun v => ?_
  have hv : v ∈ Submodule.span F (Set.range w.col) := hw ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem htMul : HtMul := by
  intro F _ _ B N n w A Λ hL
  obtain ⟨P, hP⟩ := exists_rightInv_of_span hL.spans
  refine ⟨fun a a' G G' hG hG' ha ha' => ?_, fun c hc => ?_⟩
  · exact GlobalTheory.ZeroCycleHt.formHeight_mul 0 0 hP hL.det hG hG' ha ha'
  · have h1 : IsMultiHomogeneous (fun _ : Fin B => 0) (1 : MvPolynomial (Fin B × Fin N) F) := by
      intro t ht b
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
    have := GlobalTheory.HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det one_ne_zero h1 hc
    rw [mul_one, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    exact this

end GlobalTheory.HSShort
