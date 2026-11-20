import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem comm_mem {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (F : IntermediateField k Ω) [Normal k F]
    (hc : ∀ a b : F ≃ₐ[k] F, a * b = b * a) (g h : Ω ≃ₐ[k] Ω) : g * h * (h * g)⁻¹ ∈ F.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one, hc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem sup_comm' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [Normal k Ω] (F K : IntermediateField k Ω)
    [Normal k F] [Normal k K] (hF : ∀ a b : F ≃ₐ[k] F, a * b = b * a) (hK : ∀ a b : K ≃ₐ[k] K, a * b = b * a)
    (a b : ↥(F ⊔ K) ≃ₐ[k] ↥(F ⊔ K)) : a * b = b * a := by
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥(F ⊔ K)) Ω a
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥(F ⊔ K)) Ω b
  have : g * h * (h * g)⁻¹ ∈ (F ⊔ K).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨comm_mem F hF g h, comm_mem K hK g h⟩
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one] at this
  exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.auGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), IsGalois ℚ T.L ∧ IsSolvable (T.L ≃ₐ[ℚ] T.L) := by
  intro Ω _ _ _ l _ c D T
  haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
  haveI hK : IsGalois ℚ T.K := inferInstance
  haveI : IsCyclic (T.K ≃ₐ[ℚ] T.K) := inferInstance
  haveI hF : IsGalois ℚ T.F := inferInstance
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  have hN : Normal ℚ ↥(T.F ⊔ T.K) := @IntermediateField.normal_sup ℚ Ω _ _ _ T.F T.K hF.to_normal hK.to_normal
  have hc := @sup_comm' ℚ Ω _ _ _ _ T.F T.K hF.to_normal hK.to_normal (fun a b => T.abF.is_comm.comm a b)
    (fun a b => (IsAbelianGalois.of_isCyclic ℚ T.K).is_comm.comm a b)
  rw [← T.hL] at hN hc
  exact ⟨{ to_isSeparable := inferInstance, to_normal := hN }, isSolvable_of_comm hc⟩
