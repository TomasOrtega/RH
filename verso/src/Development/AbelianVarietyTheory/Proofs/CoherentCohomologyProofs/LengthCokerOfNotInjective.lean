import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
universe u_1 u_2

namespace GlobalTheory.LengthCokernelInjective

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h : Ring.ord R (0 : R) = ⊤ := by rw [Ring.ord_eq_addVal]; simp
  have h2 : Ring.ord R (0 : R) ≤ Module.length R R :=
    Module.length_le_of_surjective (Ideal.span {(0 : R)}).mkQ (Submodule.mkQ_surjective _)
  rw [h] at h2
  exact top_le_iff.mp h2

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem length_coker_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  let a := Submodule.smithNormalFormCoeffs b h
  let t := Submodule.smithNormalFormTopBasis b h
  let s := Submodule.smithNormalFormBotBasis b h
  have hs : ∀ i, (s i : M) = a i • t i := Submodule.smithNormalFormBotBasis_def b h
  have h1 : Associated
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap))
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap)) :=
    LinearMap.associated_det_comp_equiv _ _ _
  have h2 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  have h3 : (LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap =
      Matrix.toLin t t (Matrix.diagonal a) := by
    refine t.ext fun i => ?_
    simp [hs, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [h2, h3, LinearMap.det_toLin, Matrix.det_diagonal] at h1
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr h1, addVal_finset_prod,
    (Submodule.quotientEquivPiSpan (LinearMap.range f) b h).length_eq,
    Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem length_coker_of_not_injective (f : M →ₗ[R] M) (hf : LinearMap.ker f ≠ ⊥) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 : Module.finrank R (LinearMap.ker f) ≠ 0 := by
    rwa [ne_eq, Submodule.finrank_eq_zero]
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [f.quotKerEquivRange.finrank_eq] at h2
  have h4 : Module.finrank R (M ⧸ LinearMap.range f) ≠ 0 := by omega
  rw [ne_eq, Module.finrank_eq_zero_iff] at h4
  push Not at h4
  obtain ⟨x, hx⟩ := h4
  have h5 : Function.Injective (LinearMap.toSpanSingleton R _ x) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    exact hx r h0 hr
  have h6 := Module.length_le_of_injective _ h5
  rw [length_self_eq_top] at h6
  exact top_le_iff.mp h6

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem length_coker (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.ker f = ⊥
  · exact length_coker_of_injective f (LinearMap.ker_eq_bot.mp hf)
  · rw [length_coker_of_not_injective f hf, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf]
    simp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.
-/
theorem relLength_map_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {A : Submodule R V}
    [Module.Free R A] [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    GlobalTheory.relLength A (Submodule.map g A) =
      IsDiscreteValuationRing.addVal R (LinearMap.det (LinearMap.restrict g hg)) := by
  have h : (Submodule.map g A).submoduleOf A = LinearMap.range (LinearMap.restrict g hg) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  rw [GlobalTheory.relLength_def, h, length_coker]

end GlobalTheory.LengthCokernelInjective
