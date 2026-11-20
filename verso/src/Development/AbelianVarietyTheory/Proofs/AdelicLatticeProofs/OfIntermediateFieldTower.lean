import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem bijective_mul_out_inv {H G : Type} [Group H] [Group G] (φ : H →* G)
    (hφ : Function.Injective φ) :
    Function.Bijective (fun p : H × (G ⧸ φ.range) => φ p.1 * (p.2.out)⁻¹) := by
  constructor
  · rintro ⟨h, q⟩ ⟨h', q'⟩ e
    simp only at e
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      refine ⟨h⁻¹ * h', ?_⟩
      rw [map_mul, map_inv]
      calc (φ h)⁻¹ * φ h' = (φ h)⁻¹ * (φ h' * (q'.out)⁻¹) * q'.out := by group
        _ = (φ h)⁻¹ * (φ h * (q.out)⁻¹) * q'.out := by rw [e]
        _ = _ := by group
    subst hq
    rw [hφ (mul_right_cancel e)]
  · intro g
    have : ((g⁻¹ : G) : G ⧸ φ.range).out⁻¹ * g⁻¹ ∈ φ.range := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨h, hh⟩ := this
    refine ⟨(h⁻¹, ((g⁻¹ : G) : G ⧸ φ.range)), ?_⟩
    simp only [map_inv, hh]
    group

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem TNorm.of_tower (F M E K : Type) [Field F] [Field M] [Field E] [Algebra F M] [Algebra M E]
    [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K]
    [Algebra F K] [Algebra M K] [IsScalarTower F M K] (x : F) (hx : TNorm F E K x) :
    TNorm M E K (algebraMap F M x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  let π : K ⊗[F] E →ₐ[K] K ⊗[M] E := Algebra.TensorProduct.mapOfCompatibleSMul M F K K E
  let φ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := AlgEquiv.restrictScalars_injective F
  haveI : Fintype ((E ≃ₐ[F] E) ⧸ φ.range) := Fintype.ofFinite _
  have key : ∀ (h : E ≃ₐ[M] E) (g : E ≃ₐ[F] E) (z : K ⊗[F] E),
      Algebra.TensorProduct.map (AlgHom.id K K) (h : E →ₐ[M] E)
        (π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) z)) =
      π (Algebra.TensorProduct.map (AlgHom.id K K) ((φ h * g : E ≃ₐ[F] E) : E →ₐ[F] E) z) := by
    intro h g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨π (∏ q : (E ≃ₐ[F] E) ⧸ φ.range,
    Algebra.TensorProduct.map (AlgHom.id K K) (((q.out)⁻¹ : E ≃ₐ[F] E) : E →ₐ[F] E) y), ?_⟩
  apply (algebraMap K (K ⊗[M] E)).injective
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates M E K, ← IsScalarTower.algebraMap_apply F M K x, ← hy, ← π.commutes,
    GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K, map_prod π, map_prod π,
    ← (bijective_mul_out_inv φ hφ).prod_comp (fun g : E ≃ₐ[F] E =>
      π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y)), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun q _ => key h _ y

end GlobalTheory.CNorm
