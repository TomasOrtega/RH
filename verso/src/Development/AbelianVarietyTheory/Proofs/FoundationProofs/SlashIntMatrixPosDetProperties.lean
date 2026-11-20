import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem slzDen_ne_zero (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h0 | h0
  · rw [h0] at hre
    simp at hre
    rw [Matrix.det_fin_two, h0, hre] at hδ
    simp at hδ
  · exact absurd h0 τ.im_pos.ne'

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem slzMob_im (δ : M2) (τ : ℍ) :
    ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im
      = (δ.det : ℝ) * τ.im / Complex.normSq (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [Complex.div_im, Matrix.det_fin_two]
  simp
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem slzMob_im_pos (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    0 < ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im := by
  rw [slzMob_im]
  apply div_pos
  · exact mul_pos (by exact_mod_cast hδ) τ.im_pos
  · exact Complex.normSq_pos.2 (slzDen_ne_zero δ hδ τ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem slzMob_coe (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) : ℍ) : ℂ)
      = (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [ofComplex_apply_of_im_pos (slzMob_im_pos δ hδ τ)]

/- English proof (translation)
Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem automorphyFactor_mobius_cocycle_complex (a b c d a' b' c' d' t : ℂ) (h1 : c' * t + d' ≠ 0)
    (h2 : c * ((a' * t + b') / (c' * t + d')) + d ≠ 0) :
    (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') ∧
    ((a * a' + b * c') * t + (a * b' + b * d')) / ((c * a' + d * c') * t + (c * b' + d * d'))
      = (a * ((a' * t + b') / (c' * t + d')) + b) / (c * ((a' * t + b') / (c' * t + d')) + d) := by
  have e1 : (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') := by
    field_simp
    ring
  refine ⟨e1, ?_⟩
  rw [e1]
  field_simp
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem slz_mul (k : ℕ) (f : ℍ → ℂ) (δ δ' : M2) (hδ : 0 < δ.det) (hδ' : 0 < δ'.det) :
    slz k (δ * δ') f = slz k δ' (slz k δ f) := by
  funext τ
  have h2 := slzDen_ne_zero δ hδ (ofComplex ((((δ' 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 0 1 : ℤ) : ℂ)) / (((δ' 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 1 1 : ℤ) : ℂ))))
  rw [slzMob_coe δ' hδ' τ] at h2
  obtain ⟨e1, e2⟩ := automorphyFactor_mobius_cocycle_complex ((δ 0 0 : ℤ) : ℂ) ((δ 0 1 : ℤ) : ℂ) ((δ 1 0 : ℤ) : ℂ) ((δ 1 1 : ℤ) : ℂ)
    ((δ' 0 0 : ℤ) : ℂ) ((δ' 0 1 : ℤ) : ℂ) ((δ' 1 0 : ℤ) : ℂ) ((δ' 1 1 : ℤ) : ℂ) (τ : ℂ) (slzDen_ne_zero δ' hδ' τ) h2
  simp only [slz]
  rw [slzMob_coe δ' hδ' τ, Matrix.det_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [e2, e1]
  simp only [mul_pow, mul_inv]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem slz_SL (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ) := by
  have hdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hg : ofComplex (((((γ : M2) 0 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 0 1 : ℤ) : ℂ)) / ((((γ : M2) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 1 1 : ℤ) : ℂ))) = γ • τ := by
    ext
    rw [slzMob_coe _ (by rw [hdet]; exact one_pos) τ, coe_specialLinearGroup_apply]
    simp
  simp only [slz]
  rw [hg, hdet]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem slzDen_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 :=
  slzDen_ne_zero (γ : M2) (by rw [Matrix.SpecialLinearGroup.det_coe γ]; exact one_pos) τ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem slz_continuous (k : ℕ) (f : ℍ → ℂ) (δ : M2) (hδ : 0 < δ.det) (hf : Continuous f) :
    Continuous (slz k δ f) := by
  have hw : Continuous (fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) :=
    ((continuous_const.mul continuous_coe).add continuous_const).div
      ((continuous_const.mul continuous_coe).add continuous_const) (slzDen_ne_zero δ hδ)
  have hg : Continuous (fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))) := by
    rw [isOpenEmbedding_coe.isInducing.continuous_iff]
    have : (UpperHalfPlane.coe ∘ fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))))
        = fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
      funext τ
      exact slzMob_coe δ hδ τ
    rw [this]
    exact hw
  have hj : Continuous (fun τ : ℍ => ((((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) :=
    (((continuous_const.mul continuous_coe).add continuous_const).pow k).inv₀
      (fun τ => pow_ne_zero k (slzDen_ne_zero δ hδ τ))
  exact (continuous_const.mul hj).mul (hf.comp hg)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem slz_scalar (k : ℕ) (f : ℍ → ℂ) (hk : 1 ≤ k) (n : ℕ) (τ : ℍ) (hn : 0 < n) :
    slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hτ : ofComplex ((((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ))) = τ := by
    have : (((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ)) = (τ : ℂ) := by
      simp only [Int.cast_zero, Int.cast_natCast, add_zero, zero_mul, zero_add]
      exact mul_div_cancel_left₀ _ hn'
    rw [this]
    exact ofComplex_apply τ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of]
  rw [hτ]
  push_cast
  field_simp
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem slz_props : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  intro k f hk
  refine ⟨fun δ δ' hδ hδ' => slz_mul k f δ δ' hδ hδ', fun γ τ => slz_SL k f γ τ, ?_,
    fun δ hδ hf => slz_continuous k f δ hδ hf, fun n τ hn => slz_scalar k f hk n τ hn⟩
  intro L χ
  constructor
  · intro h γ hγ
    funext τ
    have hne := pow_ne_zero k (slzDen_SL_ne_zero γ τ)
    rw [slz_SL, h γ hγ τ]
    field_simp
  · intro h γ hγ τ
    have := congrFun (h γ hγ) τ
    rw [slz_SL, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero k (slzDen_SL_ne_zero γ τ))] at this
    rw [this]
    ring

end GlobalTheory.EisM
