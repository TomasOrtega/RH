import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem dom_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := RegAtDom.map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, RegAtDom.genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := RegAtDom.genMap_stalkMap hd q hq hp s
    have hone : genMap ξ' ⟨q, hq⟩ (1 - (f.stalkMap q).hom s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hv, ht, mul_inv_cancel₀ h0, sub_self]
    have hu : IsUnit ((f.stalkMap q).hom s) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((f.stalkMap q).hom s * t) with h | h
      · exact isUnit_of_mul_isUnit_left h
      · have h' := h.map (genMap ξ' ⟨q, hq⟩)
        rw [hone] at h'
        exact absurd h' not_isUnit_zero
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem genfib_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (n : ℕ), unitAt ξ' p' (n : Ω') ↔ unitAt ξ ⟨f p'.1, h⟩ (n : Ω) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p' h n
  obtain ⟨h', hc⟩ := dom_local X Ω ξ X' Ω' ξ' i f hd p'
  have := IsCtrOf.unitAt_iff (i := i) (p := ⟨f p'.1, h⟩) (p' := p') hc (natCast_mem _ n)
  rwa [map_natCast] at this

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem dom_comp {X X₁ X₂ : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    {f : X₁ ⟶ X} {g : X₂ ⟶ X₁} {i : Ω →+* Ω₁} {k : Ω₁ →+* Ω₂} (hf : Dominates ξ₁ ξ f i)
    (hg : Dominates ξ₂ ξ₁ g k) : Dominates ξ₂ ξ (g ≫ f) (k.comp i) := by
  unfold Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem iso_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X₁ X₂ : Scheme.{0}) (Ω' : Type) [Field Ω'] (i : Ω →+* Ω') (p : Cpt ξ), (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g i → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → NormAt ξ₂ g i p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω') ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω') → NormAt ξ₁ f i p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω') p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω) → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω) p₁) → IsoAt ξ₂ (g ≫ f) (RingHom.id Ω) p) := by
  intro X Ω _ ξ X₁ X₂ Ω' _ i p
  refine ⟨fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_⟩
  · have hr : ∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → regAt ξ p = regAt ξ₁ p₁ := fun p₁ h => by
      rw [hf.regAt_eq p₁ h, Subring.map_id]
    refine ⟨fun q hq => ?_, ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q
      rw [hr ⟨_, h⟩ hq]
      exact (hn ⟨_, h⟩ hq).exists_max q rfl
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      rw [hr p₁ h₁]
      intro P hP
      obtain ⟨q, ⟨hq, hq'⟩, hqu⟩ := (hn p₁ h₁).existsUnique P hP
      refine ⟨q, ⟨(congrArg f hq).trans h₁, hq'⟩, fun q' hq'' => hqu q' ⟨?_, hq''.2⟩⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq''.1)
  · have hr : ∀ (q : Cpt ξ₂) (p₁ : Cpt ξ₁), g q.1 = p₁.1 → f p₁.1 = p.1 → regAt ξ₂ q = regAt ξ₁ p₁ :=
      fun q p₁ h h' => by rw [(hn p₁ h').regAt_eq q h, Subring.map_id]
    refine ⟨fun q hq => ?_, fun P hP => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.id_comp] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [hr q ⟨_, h⟩ rfl hq]
      exact hf.exists_max ⟨_, h⟩ hq
    · obtain ⟨p₁, ⟨h₁, h₁'⟩, hu⟩ := hf.existsUnique P hP
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, ⟨(congrArg f hq).trans h₁, (hr q p₁ hq h₁).trans h₁'⟩, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ ⟨hq'.1, (hr q' ⟨_, h⟩ rfl hq'.1).symm.trans hq'.2⟩)
  · refine ⟨?_, fun q hq => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, (congrArg f hq).trans h₁, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq')
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [(hn ⟨_, h⟩ hq).regAt_eq q rfl, Subring.map_id, hf.regAt_eq ⟨_, h⟩ hq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_iso : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ), NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) → IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  haveI loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end PositivityTheory.HtPt.Mb
