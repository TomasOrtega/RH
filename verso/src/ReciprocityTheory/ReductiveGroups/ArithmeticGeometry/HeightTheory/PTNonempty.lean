import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField Cardinal

/- English proof (translation)
Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
private lemma countable_of_intermediateField_fg {K Ω : Type} [Field K] [Countable K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨S, hS⟩ := hfg
  haveI : Countable (MvPolynomial (S : Set Ω) K) := by
    first
    | infer_instance
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinal_mk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max_lift.trans
        (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
          (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  let f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω := fun pq =>
    MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 /
      MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K (S : Set Ω) := by
      rw [hS]; exact IntermediateField.mem_top
    obtain ⟨r, hr, t, ht, rfl⟩ := (IntermediateField.mem_adjoin_iff_div).mp hx
    rw [Algebra.adjoin_eq_range] at hr ht
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := ht
    exact ⟨(p, q), rfl⟩
  exact hf.countable

/- English proof (translation)
Treat this case separately. Treat this case separately. Equip the data with the indicated structure. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately. Establish an intermediate fact.

Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Equip the data with the indicated structure. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by
  haveI hKc : Countable K := by
    first
    | infer_instance
    | exact (Module.finBasis ℚ K).equivFun.injective.countable
  haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg
  letI : Algebra K ℂ := sg.toAlgebra
  haveI : FaithfulSMul K ℂ := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K ℂ).mpr sg.injective
  haveI : FaithfulSMul K Ω := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K Ω).mpr (algebraMap K Ω).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hKle : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have htt : Cardinal.aleph0 < Cardinal.mk t := by
    first
    | (by_contra hle
       have h := IsAlgClosed.cardinal_le_max_transcendence_basis _ ht
       exact absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))
    | (have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC
       rw [Cardinal.lift_inj] at h
       rw [h] at hC
       exact hC)
  have hst : Cardinal.mk s ≤ Cardinal.mk t := Cardinal.mk_le_aleph0.trans htt.le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hst
  let u : s → ℂ := fun i => ((e i : t) : ℂ)
  have hu : AlgebraicIndependent K u := ht.1.comp e e.injective
  let E := hs.1.aevalEquiv.symm.trans hu.aevalEquiv
  let φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ :=
    (Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp E.injective
  letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    hs.isAlgebraic
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    NoZeroSMulDivisors.of_algebraMap_injective hφ
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective
  let g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_⟩
  ext k
  have h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω
      (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k) := by
    first
    | rfl
    | exact IsScalarTower.algebraMap_apply _ _ _ k
  show g (algebraMap K Ω k) = sg k
  rw [h1, g.commutes]
  exact φ.commutes k

end ReciprocityTheory.ChartRestriction.G.T0
