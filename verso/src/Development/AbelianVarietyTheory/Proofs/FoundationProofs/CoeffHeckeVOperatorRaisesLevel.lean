import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

def scaleH (l : ℕ) (hl : 0 < l) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk ((l : ℂ) * τ) (by simp; positivity)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma coe_sl_apply (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma denom_sl_ne (g : SL(2, ℤ)) (z : ℍ) : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h2 := UpperHalfPlane.denom_ne_zero g z
  simpa [UpperHalfPlane.denom] using h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use the polynomial consequences of the given equalities and inequalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem Vo_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l →
    (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  intro k L l χ a hl
  have key : MF k L χ a → MF k (L * l) χ (Vo l a) := by
    rintro ⟨hP, hI⟩
    obtain ⟨hP', hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hP
    refine ⟨hP', ?_⟩
    intro γ hγ τ
    obtain ⟨m, hm⟩ := hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    let γ' : SL(2, ℤ) := ⟨!![γ 0 0, (l : ℤ) * γ 0 1; (L : ℤ) * m, γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hm] at hdet; push_cast at hdet; linear_combination hdet⟩
    have h1 : ((L : ℕ) : ℤ) ∣ γ' 1 0 := ⟨m, by simp [γ']⟩
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hc : ((γ 1 0 : ℤ) : ℂ) = (L : ℂ) * l * m := by rw [hm]; push_cast; ring
    have e1 : γ' • scaleH l hl τ = scaleH l hl (γ • τ) := by
      apply UpperHalfPlane.ext
      rw [coe_sl_apply]
      simp only [scaleH, UpperHalfPlane.coe_mk, coe_sl_apply]
      have hd := denom_sl_ne γ τ
      rw [hc] at hd ⊢
      simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      push_cast
      have hd2 : (L : ℂ) * m * (l * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
        convert hd using 1; ring
      field_simp
    rw [hq (γ • τ) (scaleH l hl (γ • τ)) rfl, hq τ (scaleH l hl τ) rfl, ← e1, hI γ' h1]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, scaleH, UpperHalfPlane.coe_mk]
    rw [hc]; push_cast; ring_nf
  refine ⟨key, ?_⟩
  rintro ⟨hM, C, hC⟩
  refine ⟨key hM, C, fun τ => ?_⟩
  obtain ⟨_, hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hM.1
  rw [hq τ (scaleH l hl τ) rfl]
  have him : (scaleH l hl τ).im = l * τ.im := by
    change ((l:ℂ) * (τ:ℂ)).im = (l:ℝ) * (τ:ℂ).im
    simp
  have hle : τ.im ≤ (scaleH l hl τ).im := by
    rw [him]; have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith [τ.im_pos]
  calc ‖qs a (scaleH l hl τ)‖ ^ 2 * τ.im ^ k ≤ ‖qs a (scaleH l hl τ)‖ ^ 2 * (scaleH l hl τ).im ^ k := by
        gcongr
    _ ≤ C := hC _

end GlobalTheory
