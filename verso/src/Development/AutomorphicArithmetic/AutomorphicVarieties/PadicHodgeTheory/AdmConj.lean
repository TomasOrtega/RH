import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem kur_map {l : ℕ} [Fact l.Prime] (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    g x ∈ MaximalUnramifiedExtension l := by
  have h1 : g x ∈ (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    (Set.mem_image_of_mem _ hx :)
  rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map] at h1
  refine (IntermediateField.adjoin_le_iff.mpr ?_) h1
  rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
private theorem iq_normal (l : ℕ) [Fact l.Prime] : (Iq l).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (kur_map g⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

section Gen

variable {Q Γ G A V B : Type} [Field Q] [Group Γ] [Group G] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V]
  [Module Q V] [IsScalarTower Q A V] [CommRing B] [Algebra Q B] (α : Γ →* (B ≃ₐ[Q] B))

private noncomputable def cj (c : Γ) : V ⊗[Q] B ≃ₗ[A] V ⊗[Q] B :=
  AlgebraTensorModule.congr (LinearEquiv.refl A V) (α c).toLinearEquiv

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately.
-/
private theorem cj_act (c g : Γ) (f : V →ₗ[A] V) (x : V ⊗[Q] B) :
    AlgebraTensorModule.map f (α (c * g * c⁻¹)).toLinearMap (cj (A := A) α c x) =
      cj (A := A) α c (AlgebraTensorModule.map f (α g).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have h : α (c * g * c⁻¹) (α c b) = α c (α g b) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
    simp only [cj, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem cj_one (c : Γ) (v : V) : cj (A := A) α c (v ⊗ₜ[Q] (1 : B)) = v ⊗ₜ[Q] (1 : B) := by
  simp [cj]

/- English proof (translation)
Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem finrank_inv (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) :
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) =
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (φ g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) := by
  symm
  refine ((cj (A := A) α c).ofSubmodules _ _ ?_).finrank_eq
  ext x
  obtain ⟨y, rfl⟩ := (cj (A := A) (V := V) α c).surjective x
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, (cj α c).injective.eq_iff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem cob_iff (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) (z : G → V) :
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap x - x) ↔
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g) (α (φ g)).toLinearMap x - x) := by
  rw [(cj (A := A) (V := V) α c).surjective.exists]
  refine exists_congr fun y => forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, ← map_sub, ← cj_one (A := A) α c, (cj α c).injective.eq_iff, cj_one]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem index_conj (c : Γ) (φ : G →* Γ) (N : Subgroup Γ) [hN : N.Normal] :
    (((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N).index = (φ.range ⊔ N).index := by
  have h1 : N.map (MulAut.conj c).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy c
    · intro hx
      refine ⟨c⁻¹ * x * c⁻¹⁻¹, hN.conj_mem x hx c⁻¹, ?_⟩
      simp [mul_assoc]
  have h2 : ((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N = (φ.range ⊔ N).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_sup, h1, MonoidHom.range_comp]
  rw [h2]
  exact Subgroup.index_map_of_bijective (MulAut.conj c).bijective _

end Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Loc.admissible_conjugate :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (c : GQ l), (IsCr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsCr φ ρ) ∧ (IsDr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsDr φ ρ) ∧ UpperTheory.V.Loc.finiteCocycles ((MulAut.conj c).toMonoidHom.comp φ) ρ = UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro l _ G _ _ _ φ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ c
  refine ⟨?_, ?_, ?_⟩
  · haveI := iq_normal l
    have h1 : finrank ℚ_[l] ↥(Dcr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQ c φ (resCoef ℚ_[l] ρ)
    rw [IsCr, IsCr, h1, index_conj]
  · have h1 : finrank ℚ_[l] ↥(Ddr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQdR c φ (resCoef ℚ_[l] ρ)
    have h2 := index_conj c φ ⊥
    rw [sup_bot_eq, sup_bot_eq] at h2
    rw [IsDr, IsDr, h1, h2]
  · ext z
    exact and_congr_right fun _ => cob_iff (PP l).actQ c φ ρ z
