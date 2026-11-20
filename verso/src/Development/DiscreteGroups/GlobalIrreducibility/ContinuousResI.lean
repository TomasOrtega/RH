import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem res_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Dec (F := E) A := by
  rw [mem_Dec] at hσ ⊢
  have key : ∀ x, x ∈ (AlgEquiv.restrictScalars E σ) • A ↔ x ∈ σ • A := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  ext x
  rw [key, hσ]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem res_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Ine (F := E) A :=
  ⟨res_mem_Dec hσ.1, hσ.2⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem res_actsAs {q q' n a b : ℕ} (hq : q' = q ^ n) {σ : G E' Ω} (hσ : ActsAs A q' σ a b) :
    ActsAs A q (AlgEquiv.restrictScalars E σ) (n * a) (n * b) := by
  refine ⟨res_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [hq, ← pow_mul, ← pow_mul] at this
  exact this

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

def resW {n : ℕ} (hq : normV w' = normV w ^ n) : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalars E (σ : G E' Ω), by
    obtain ⟨a, b, hab⟩ := σ.2
    exact ⟨n * a, n * b, res_actsAs hq hab⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_resW {n : ℕ} (hq : normV w' = normV w ^ n) (σ : Weil h') :
    ((resW h h' hq σ : Weil h) : G E Ω) = AlgEquiv.restrictScalars E (σ : G E' Ω) := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_resW {n : ℕ} (hq : normV w' = normV w ^ n) (σ : Weil h') : deg (resW h h' hq σ) = n * deg σ := by
  obtain ⟨a, b, hab⟩ := σ.2
  rw [deg_eq (σ := resW h h' hq σ) (res_actsAs hq hab), deg_eq hab]
  push_cast; ring

def resI : Ine (F := E') A →* Ine (F := E) A where
  toFun t := ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resW_ineIncl {n : ℕ} (hq : normV w' = normV w ^ n) (t : Ine (F := E') A) :
    resW h h' hq (ineIncl h' t) = ineIncl h (resI t) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro U hU
  obtain ⟨F, hF, hFU⟩ : ∃ F : IntermediateField E Ω, FiniteDimensional E F ∧
      (F.fixingSubgroup : Set (Ω ≃ₐ[E] Ω)) ⊆ U := by
    first
      | exact (krullTopology_mem_nhds_one_iff E Ω U).mp hU
      | (obtain ⟨V, hV, hVU⟩ := (galGroupBasis E Ω).nhds_one_hasBasis.mem_iff.mp hU
         obtain ⟨H, ⟨F, hF, rfl⟩, rfl⟩ := (mem_galBasis_iff E Ω V).mp hV
         exact ⟨F, hF, hVU⟩)
  obtain ⟨t, ht⟩ : F.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    first
      | exact (Submodule.fg_iff_finiteDimensional _).mpr hF
      | exact Module.Finite.iff_fg.mp hF
  have hint : ∀ x ∈ (t : Set Ω), IsIntegral E' x := by
    intro x _
    first
      | exact Algebra.IsIntegral.isIntegral x
      | exact ((IsAlgClosure.isAlgebraic (R := E') (K := Ω)).isAlgebraic x).isIntegral
      | exact (IsAlgClosure.algebraic (R := E') (K := Ω) x).isIntegral
  have hfin : FiniteDimensional E' (IntermediateField.adjoin E' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : F ≤ (IntermediateField.adjoin E' (t : Set Ω)).restrictScalars E := by
    rw [← ht, IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin E' (t : Set Ω) hy
  have hopen := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin E' (t : Set Ω))
  refine Filter.mem_of_superset
    (hopen.mem_nhds (IntermediateField.adjoin E' (t : Set Ω)).fixingSubgroup.one_mem) ?_
  intro σ hσ
  apply hFU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  first
    | exact hσ x (hle hx)
    | exact hσ x ((IntermediateField.mem_restrictScalars E).mp (hle hx))
    | simpa using hσ x (hle hx)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem continuous_resI : Continuous (resI (E := E) (E' := E') (Ω := Ω) (A := A)) := by
  apply Continuous.subtype_mk
  exact (continuous_res (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val

end DiscreteGroups.sglob.DzType

end
