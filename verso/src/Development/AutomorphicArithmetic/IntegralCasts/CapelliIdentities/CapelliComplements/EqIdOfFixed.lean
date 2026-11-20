import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

namespace Bl.EqIdOfFixed

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private lemma ne_id_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h
  obtain ⟨-, hc, -, hs⟩ := h
  by_contra hne0
  have hne : ∀ z : E, σ z = z := fun z => by_contra fun hz => hne0 ⟨z, hz⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := hc
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have := hs τ z
  rw [hne z] at this
  exact this.symm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Supply the required witnesses or components. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private lemma eq_id_of_fix {F E : Type} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) {x : E} (hx : σ x = x)
    (hno : ∀ t : F, algebraMap F E t ≠ x) (y : E) : σ y = y := by
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hno (-(s / t))
      have h1 : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : x = t⁻¹ • -(s • (1 : E)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hc : Fintype.card (Fin 2) = Module.finrank F E := by simp [hd]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E) := by
    apply b.ext
    intro i
    fin_cases i
    · simp [b]
    · simp [b, hx]
  exact LinearMap.congr_fun heq y

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {F E : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F] [inst_2 : Field.{0} E] [inst_3 : NumberField.{0} E]
  [inst_4 : Algebra.{0, 0} F E] {σ : AlgHom.{0, 0, 0} F E E},
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
    ∀ {x : E},
      Eq.{1} (DFunLike.coe.{1, 1, 1} σ x) x →
        Exists.{1} fun (t : F) ↦ Eq.{1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} F E) t) x := by
  intro F E _ _ _ _ _ σ h x hx
  by_contra hno0
  have hno : ∀ t : F, algebraMap F E t ≠ x := fun t ht => hno0 ⟨t, ht⟩
  obtain ⟨y, hy⟩ := ne_id_of_cm σ h
  have h' := h
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'
  exact hy (eq_id_of_fix h'.2.2.1 σ hx hno y)

end Bl.EqIdOfFixed
