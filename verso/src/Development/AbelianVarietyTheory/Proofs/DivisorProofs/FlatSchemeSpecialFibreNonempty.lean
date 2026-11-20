import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.FlatDVRFibre

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_basicOpen_unif_iff {O : Type} [CommRing O] {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (ϖ : O) (z : Z) :
    z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ↔ ϖ ∉ (f z).asIdeal := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem genericPoint_mem_and_exists_not_mem :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)), Flat f → Nonempty (specialFibre f) →
  genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ∧ ∃ z : Z, z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) := by
  intro O _ _ _ ϖ hϖ Z _ f hf hne
  refine ⟨?_, ?_⟩
  · rw [mem_basicOpen_unif_iff]
    let e : Spec (.of O) := (⊥ : PrimeSpectrum O)
    have hη : e ⤳ f (genericPoint Z) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum O))
    obtain ⟨x', hx', hx''⟩ := Flat.generalizingMap f hη
    have hxe : x' = genericPoint Z :=
      (hx'.antisymm (genericPoint_specializes x')).eq
    rw [← hxe, hx'']
    change ϖ ∉ (⊥ : Ideal O)
    simpa using hϖ.ne_zero
  · obtain ⟨p⟩ := hne
    refine ⟨specialι f p, ?_⟩
    rw [mem_basicOpen_unif_iff, not_not]
    have h1 : f (specialι f p) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p) := by
      let p' : ↑(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := p
      change f (pullback.fst f _ p') = _
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    set q := pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p
    change ϖ ∈ Ideal.comap (IsLocalRing.residue O) q.asIdeal
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [hq, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.FlatDVRFibre
