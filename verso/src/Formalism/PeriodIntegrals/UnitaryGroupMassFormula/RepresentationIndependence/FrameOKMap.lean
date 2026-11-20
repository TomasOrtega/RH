import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.IsFixedConvMap
import Formalism.PeriodIntegrals.RepsIndep

noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.UniformConstantsAndStatements

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem cntCl_equiv {α : Type} (f g : α → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ a, f (g a) = a)
    (X Y : Set α) (R R' : α → α → Prop)
    (hX : ∀ a, f a ∈ Y ↔ a ∈ X) (hR : ∀ a b, R' (f a) (f b) ↔ R a b) :
    Cnt.cntCl Y R' = Cnt.cntCl X R := by
  have hinj : Function.Injective (fun O : Set α => f ⁻¹' O) := by
    intro O O' h
    ext y
    have := Set.ext_iff.mp h (g y)
    simpa only [Set.mem_preimage, hfg] using this
  have himg : (fun O : Set α => f ⁻¹' O) '' {O | ∃ a ∈ Y, O = {b | b ∈ Y ∧ R' a b}} =
      {O | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} := by
    ext O
    constructor
    · rintro ⟨O', ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨g y, (hX (g y)).mp (by rw [hfg]; exact hy), ?_⟩
      ext c
      rw [← hfg y]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hX, hR, hgf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨{b | b ∈ Y ∧ R' (f a) b}, ⟨f a, (hX a).mpr ha, rfl⟩, ?_⟩
      ext c
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hX, hR]
  unfold Cnt.cntCl
  rw [← himg, hinj.injOn.encard_image]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem XS_map {T : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : FlagG (VS D) D.R.rS T) : XS D (mapF γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (XS D F) := by
  unfold XS Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • F.e a, ⟨a, x, hx, rfl⟩, by simp [mapF]⟩
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by simp [mapF]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem FrameOK_map {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F' : LFlag (VS D) D.R.rS T'} (h : FrameOK D Λ F') :
    FrameOK D (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F') := by
  unfold FrameOK at h ⊢
  refine ⟨IsFixedConv_map hγ h.1, ?_⟩
  rw [XLam_mapL hγ, h.2]
  exact (XS_map hγ F'.fl).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Substitute using the available equality. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem EZ_map {T T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Cnt.LatV D} {F : LFlag (Lat.hS D) D.R.rS T} {Z : Cnt.GramM D} {F' : LFlag (Lat.hS D) D.R.rS T'}
    (h : F' ∈ EZ D T' Λ F Z) : mapL γ hγ F' ∈ EZ D T' (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) Z := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, IsGeneric_map hγ h2, ?_⟩
  · unfold IsNormFrame at h1 ⊢
    obtain ⟨k1, k2, k3⟩ := h1
    exact ⟨IsLift_map hγ k1, AdmWit_map hγ k2, FrameOK_map hγ k3⟩
  · subst h3
    unfold ZhatL
    exact Zhat_mapF hγ F.fl F'.fl

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem cntZ_map {T : D.host.E} (T' : D.host.E) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : Cnt.LatV D) (F : LFlag (Lat.hS D) D.R.rS T) (Z : Cnt.GramM D) :
    cntZ D T' (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) Z = cntZ D T' Λ F Z := by
  unfold cntZ
  have hγ' := iso_symm hγ
  have hΛ : Formalism.HermitianLatticesTheory.gmap γ.symm (Formalism.HermitianLatticesTheory.gmap γ Λ) = Λ := by
    ext x
    simp [Formalism.HermitianLatticesTheory.gmap]
  refine cntCl_equiv (mapL γ hγ) (mapL γ.symm hγ') (mapL_symm hγ) (fun a => ?_) _ _ _ _
    (fun a => ?_) (fun a b => ?_)
  · first
      | exact mapL_symm hγ' a
      | simpa using mapL_symm hγ' a
  · constructor
    · intro h
      have := EZ_map hγ' h
      rwa [hΛ, mapL_symm hγ, mapL_symm hγ] at this
    · exact EZ_map hγ
  · constructor
    · intro h
      have := rel_map hγ' h
      rwa [hΛ, mapL_symm hγ, mapL_symm hγ, mapL_symm hγ] at this
    · exact rel_map hγ

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem lf_map {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {γ₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ₀ ∈ stabF D F0)
    (hfix : ∀ a, γ₀ (F0.e a) = F0.e a) : mapL γ₀ hγ.1 (lf D F0) = lf D F0 := by
  have hz : γ₀ F0.z = F0.z := hγ.2.2
  unfold lf mapL mapF
  congr 1
  all_goals first
    | exact hz
    | (cases F0; simp only [FlagG.mk.injEq]; exact ⟨funext hfix, hz⟩)

end PI.RepsIndep.Tr

namespace PI.RepsIndep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.UniformConstantsAndStatements

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem stepCnt (D : D7) : StepCnt D := by
  unfold StepCnt
  intro T T' F0 Λ _ γ₀ hγ hfix Z
  have h := PI.RepsIndep.Tr.cntZ_map T' hγ.1 Λ (lf D F0) Z
  rwa [PI.RepsIndep.Tr.lf_map F0 hγ hfix] at h

end PI.RepsIndep
