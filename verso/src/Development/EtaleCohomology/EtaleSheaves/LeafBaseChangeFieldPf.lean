import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut

noncomputable section
open Polynomial IntermediateField

namespace LateralTheory.E.LeafBaseChangeFieldPf

def ratMap (F G : Type) [Field F] [Field G] [Algebra F G] : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom (algebraMap F G))) (show
      nonZeroDivisors F[X] ≤ Submonoid.comap ((algebraMap G[X] (RatFunc G)).comp
        (Polynomial.mapRingHom (algebraMap F G))) (nonZeroDivisors (RatFunc G)) from by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    intro h
    apply hp0
    have h1 := RatFunc.algebraMap_injective G (h.trans (map_zero _).symm)
    exact (Polynomial.map_eq_zero_iff (algebraMap F G).injective).1 h1)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma ratMap_algebraMap (F G : Type) [Field F] [Field G] [Algebra F G] (f : F) :
    ratMap F G (algebraMap F (RatFunc F) f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
  have e1 : algebraMap F (RatFunc F) f = algebraMap F[X] (RatFunc F) (C f) / algebraMap F[X] (RatFunc F) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [e1, ratMap, RatFunc.liftRingHom_apply_div]
  simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma mem_adjoin_of_ratFunc {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] (x : RatFunc G) :
    algebraMap (RatFunc G) L x ∈ G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := by
  have key : ∀ p : G[X], algebraMap (RatFunc G) L (algebraMap G[X] (RatFunc G) p) =
      aeval (algebraMap (RatFunc G) L RatFunc.X) p := by
    intro p
    rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom x, map_div₀, key, key]
  exact div_mem (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))
    (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma transc_X_image {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] : Transcendental G (algebraMap (RatFunc G) L RatFunc.X) := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_algebraMap_apply, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap] at h
  exact RatFunc.algebraMap_injective G ((algebraMap (RatFunc G) L).injective h)

/- English proof (translation)
Introduce a local definition for the expression. Equip the data with the indicated structure. A detailed English derivation is pending.
-/
lemma finite_over_adjoin {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] [Module.Finite (RatFunc G) L] :
    FiniteDimensional G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L := by
  let c : RatFunc G →+* G⟮algebraMap (RatFunc G) L RatFunc.X⟯ :=
    (algebraMap (RatFunc G) L).codRestrict _ mem_adjoin_of_ratFunc
  letI : Algebra (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := c.toAlgebra
  haveI : IsScalarTower (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc G) _ L

end LateralTheory.E.LeafBaseChangeFieldPf

open LateralTheory.E.LeafBaseChangeFieldPf in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := by
  intro F G K _ _ _ _ _ t ht hfin
  let e := RatFunc.algEquivOfTranscendental t ht
  let h : F⟮t⟯ →+* RatFunc G := (ratMap F G).comp e.symm.toRingHom
  letI : Algebra F⟮t⟯ (RatFunc G) := h.toAlgebra
  haveI : Nontrivial (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ h.injective
      (algebraMap F⟮t⟯ K).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct F⟮t⟯ (RatFunc G) K)
  letI : Field (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Module.Finite.base_change F⟮t⟯ (RatFunc G) K
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc G) M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsScalarTower G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := inferInstance
  refine ⟨TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M, inferInstance, inferInstance,
    algebraMap (RatFunc G) _ RatFunc.X,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := F⟮t⟯) (A := RatFunc G) (B := K)).toRingHom,
    transc_X_image, finite_over_adjoin, ?_⟩
  ext f
  have h1 : h (algebraMap F F⟮t⟯ f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
    show ratMap F G (e.symm (algebraMap F F⟮t⟯ f)) = _
    rw [AlgEquiv.commutes]
    exact ratMap_algebraMap F G f
  rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F⟮t⟯ K, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F⟮t⟯ (RatFunc G)]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M), ← h1]
  rfl
