import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  obtain ⟨y, rfl⟩ : z ∈ Set.range (X.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact hz
  have hinj := h.inj ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := hinj.isDomain (genMap ξ ⟨p, hp⟩)
  have hp' : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ p := hp
  let φ := X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ
  have hφ : Spec.map φ ≫ X.fromSpecStalk p = ξ := by
    change Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = ξ
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hbot : (Spec.map φ) (IsLocalRing.closedPoint Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (genMap ξ ⟨p, hp⟩) (IsLocalRing.maximalIdeal Ω) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  have hη : genPt ξ = X.fromSpecStalk p ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [← hbot]
    conv_lhs => rw [genPt, ← hφ]
    rfl
  rw [hη]
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (X.fromSpecStalk p).continuous

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
