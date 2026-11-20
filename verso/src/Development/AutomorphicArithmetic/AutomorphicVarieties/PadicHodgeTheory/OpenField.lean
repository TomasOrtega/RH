import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OpenFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem open_fix {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    (IntermediateField.fixedField H).fixingSubgroup = H :=
  _root_.UpperTheory.Reformulated.B.Qi42.open_fix H hH

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem open_index {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    H.index = finrank ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, open_fix H hH]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem open_fin {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    FiniteDimensional ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [← InfiniteGalois.isOpen_iff_finite, open_fix H hH]
  exact hH

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem fixed_sup {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) :
    IntermediateField.fixedField (H ⊔ Iq v) = IntermediateField.fixedField H ⊓ MaximalUnramifiedExtension v := by
  have h1 : IntermediateField.fixedField (Iq v) = MaximalUnramifiedExtension v := InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v)
  rw [← h1]
  apply le_antisymm
  · exact le_inf (IntermediateField.fixedField_le le_sup_left) (IntermediateField.fixedField_le le_sup_right)
  · rw [IntermediateField.le_iff_le]
    refine sup_le ?_ ?_
    · rw [← IntermediateField.le_iff_le]; exact inf_le_left
    · rw [← IntermediateField.le_iff_le]; exact inf_le_right

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Loc.openField :
    ∀ {v : ℕ} [Fact v.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ), ∃ (K : FinExt v) (e : G ≃* ↥(GK K)), Continuous e ∧ Continuous e.symm ∧ (GK K).subtype.comp e.toMonoidHom = φ ∧ φ.range = GK K ∧ φ.range.index = finrank ℚ_[v] ↥K.1 ∧ (φ.range ⊔ Iq v).index = finrank ℚ_[v] ↥(K0 K) := by
  intro v _ G _ _ _ φ hφ
  have hH : IsOpen (φ.range : Set (GQ v)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  let K : FinExt v := ⟨IntermediateField.fixedField φ.range, open_fin _ hH⟩
  have hK : φ.range = GK K := (open_fix _ hH).symm
  let e : G ≃* ↥(GK K) := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hK)
  have he : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => rfl
  refine ⟨K, e, ?_, ?_, ?_, hK, open_index _ hH, ?_⟩
  · exact continuous_induced_rng.2 hφ.continuous
  · rw [hφ.isInducing.continuous_iff]
    have : φ ∘ e.symm = Subtype.val := by
      funext x
      rw [Function.comp_apply, ← he, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val
  · ext1 g
    exact he g
  · rw [open_index _ (Subgroup.isOpen_mono le_sup_left hH), fixed_sup]
    rfl
