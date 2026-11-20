import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LabTies

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    G E Ω →* G E Ω where
  toFun := GlobalTheory.AntiRamConj.conjAut c hc
  map_one' := by
    ext x
    exact c.apply_symm_apply x
  map_mul' g h := by
    ext x
    change c (g (h (c.symm x))) = c (g (c.symm (c (h (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjHom_apply (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (g : G E Ω) (x : Ω) : conjHom c hc g x = c (g (c.symm x)) := rfl

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `U hU`. Take `⟨L, hL, hLU⟩` from `(krullTopology_mem_nhds_one_iff E Ω U).1 hU`. Take `⟨S, hS⟩` from `IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))`.

Set `L'` to `IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)`. Establish `hL' : FiniteDimensional E L'` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Use `Filter.mem_map.2 (Filter.mem_of_superset ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)` and prove the remaining obligations. Rewrite `hg` using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Establish `key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g))`.

Rewrite using `[← hS, IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Establish `h1 : conjHom c hc g x = x`.

Rewrite using `[conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]`. Conclude with `(Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)`.
-/
theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) : Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)
  have hL' : FiniteDimensional E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.2 (Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  have key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : conjHom c hc g x = x := by
      rw [conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)

/- English proof (translation)
Establish `hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y` using `hc'`. Establish `eB : B' = GlobalTheory.AntiRamConj.moveVal c B`. Use extensionality with `y`. Rewrite using `[GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]`. Establish `eγ : γ' = conjHom c hc γ`.

Use extensionality with `y`. Rewrite using `[conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]`. Substitute `eB eγ` using the available equality. Use `set f := conjHom c hc`. Use `⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩` and prove the remaining obligations.

Establish `h1` using `GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ`. Establish `e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B`. Use extensionality with `x`. Simplify using `[GlobalTheory.AntiRamConj.mem_moveVal]`. Rewrite `h1` using `[e2]`.

Establish `e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ)`. Use extensionality with `x`. Rewrite using `[conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]`. Simplify using the standard rewrite rules. Rewrite using `[e3]`.

Use `map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_` and prove the remaining obligations. Establish `h2` using `Subgroup.mem_map_of_mem f hτ`. Rewrite `h2` using `[MonoidHom.map_closure]`. Use `Subgroup.closure_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha | ha, rfl⟩`.

Conclude with `Or.inl (congrArg f ha)`. Use `Or.inr fun y hy => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]`. Conclude with `ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)`.
-/
theorem tameGenAt_transport (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y)
    {B B' : ValuationSubring Ω} (hB : ∀ y, y ∈ B ↔ c y ∈ B') {γ γ' : G E Ω} (hγ : ∀ y, γ' (c y) = c (γ y))
    (h : TameGenAt B γ) : TameGenAt B' γ' := by
  have hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y := hc'
  have eB : B' = GlobalTheory.AntiRamConj.moveVal c B := by
    ext y
    rw [GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]
  have eγ : γ' = conjHom c hc γ := by
    ext y
    rw [conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]
  subst eB eγ
  set f := conjHom c hc
  refine ⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ
  have e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B := by
    ext x
    simp [GlobalTheory.AntiRamConj.mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ) := by
    ext x
    rw [conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

/- English proof (translation)
Introduce `D T ⟨γ, h1, h2, h3⟩`. Establish `hG : GenFam D γ`. Use `⟨h1, fun k w hw => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl | hv⟩` from `GlobalTheory.TypePlaceCover.place_cover D k w hw`. Rewrite using `[h1]`.

Conclude with `D.ntypes.tg_gen k v`. Take `⟨c, hc1, hc2, hc3⟩` from `h2 k v w hv`. Use `tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3 (D.ntypes.tg_gen k v)` and prove the remaining obligations. Rewrite using `[RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]`. Establish `h3' : GlobalTheory.PendOf.Model.LabAll T γ` using `h3`.

Conclude with `⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3', GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩`.
-/
theorem main : ∀ (D : D7) (T : WDTie D.nd D.naut), LabAll D T → IneRep D ∧ LabDepth D ∧ LabGen D := by
  intro D T ⟨γ, h1, h2, h3⟩
  have hG : GenFam D γ := by
    refine ⟨h1, fun k w hw => ?_⟩
    obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1]
      exact D.ntypes.tg_gen k v
    · obtain ⟨c, hc1, hc2, hc3⟩ := h2 k v w hv
      refine tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3
        (D.ntypes.tg_gen k v)
      rw [RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]
  have h3' : GlobalTheory.PendOf.Model.LabAll T γ := h3
  exact ⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3',
    GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩

end GlobalTheory.LabTies

end
