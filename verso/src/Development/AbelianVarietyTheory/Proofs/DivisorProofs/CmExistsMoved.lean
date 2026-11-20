import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem cm_exists_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : (∃ α : E, σ α ≠ α) ∧ ∀ x, σ (σ x) = x := by
  obtain ⟨_, hc, _, hconj⟩ := h
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply w.embedding.injective
    rw [hconj, hconj, star_star]
  refine ⟨?_, hinv⟩
  by_contra hne
  push_neg at hne
  have hw : w.IsComplex := hc.isComplex w
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hconj w.embedding x
  rw [hne] at hx
  exact hx.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem quad_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, ∃ δ : Fv F v ⊗[F] E, IsQuad (GlobalTheory.HoweLocal.cv σ v) δ := by
  intro F E _ _ _ _ _ σ h v
  have hdim : Module.finrank F E = 2 := h.2.2.1
  obtain ⟨⟨α, hα⟩, hinv⟩ := cm_exists_moved F E σ h
  set δ₀ : E := α - σ α with hδ₀
  have hanti : σ δ₀ = -δ₀ := by
    rw [hδ₀, map_sub, hinv]; ring
  have hne : δ₀ ≠ 0 := by
    intro h0; apply hα; rw [hδ₀, sub_eq_zero] at h0; exact h0.symm
  have hli : LinearIndependent F ![(1 : E), δ₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : σ (s • (1 : E) + t • δ₀) = s • (1 : E) - t • δ₀ := by
      simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hanti]
      ring
    rw [hst, map_zero] at h2
    have ht : (2 * t) • δ₀ = 0 := by
      have : (s • (1 : E) + t • δ₀) - (s • (1 : E) - t • δ₀) = (2 * t) • δ₀ := by
        rw [mul_smul, two_smul]; abel
      rw [← this, hst, ← h2, sub_zero]
    have ht0 : t = 0 := by
      rcases smul_eq_zero.mp ht with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
      · exact absurd h3 hne
    refine ⟨?_, ht0⟩
    rw [ht0, zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h3 | h3
    · exact h3
    · exact absurd h3 one_ne_zero
  let b0 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : ∀ i, b0 i = ![(1 : E), δ₀] i := fun i => by
    simp [b0, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] δ₀, ⟨?_, ?_, ?_⟩⟩
  · have hu : IsUnit δ₀ := hne.isUnit
    have := hu.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)
    simpa [Algebra.TensorProduct.includeRight_apply] using this
  · simp [GlobalTheory.HoweLocal.cv, Algebra.TensorProduct.map_tmul, hanti, TensorProduct.tmul_neg]
  · refine ⟨Algebra.TensorProduct.basis (Fv F v) b0, ?_, ?_⟩
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl

end GlobalTheory.HoweLocal
