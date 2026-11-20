import Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ProperBaseChangeClosedFiberStrictlyHenselianEqui

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafPtWPf

/- English proof (translation)
Introduce `A _ _ B W ι _ s hx`. Use `set t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s with ht`. Establish `hcl : IsClosed (s.base ⁻¹' Set.range ι.base)` using `(ι.isClosedEmbedding.isClosed_range).preimage s.continuous`. Take `⟨x, hx⟩` from `hx`. Establish `hc : s.base (IsLocalRing.closedPoint A) ∈ Set.range ι.base` using `(IsLocalRing.specializes_closedPoint (R := A) x).mem_closed hcl hx`.

Establish `: Surjective (pullback.fst t ι)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]`. Introduce `y`. Simplify using `only [Set.mem_preimage]`.

Establish `hy : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).base y = IsLocalRing.closedPoint A`. Establish `: y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A)` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue A)`. Rewrite using `[ht, Scheme.Hom.comp_base, TopCat.comp_app, hy]`.

Conclude with `hc`. Use `haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst t ι)`. Use `⟨inv (pullback.fst t ι) ≫ pullback.snd t ι, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]`.
-/
theorem closedLift : LeafClosedLift := by
  intro A _ _ B W ι _ s hx
  set t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s with ht
  have hcl : IsClosed (s.base ⁻¹' Set.range ι.base) :=
    (ι.isClosedEmbedding.isClosed_range).preimage s.continuous
  obtain ⟨x, hx⟩ := hx
  have hc : s.base (IsLocalRing.closedPoint A) ∈ Set.range ι.base :=
    (IsLocalRing.specializes_closedPoint (R := A) x).mem_closed hcl hx
  have : Surjective (pullback.fst t ι) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro y
    simp only [Set.mem_preimage]
    have hy : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).base y = IsLocalRing.closedPoint A := by
      have : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
      subst this
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    rw [ht, Scheme.Hom.comp_base, TopCat.comp_app, hy]
    exact hc
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst t ι)
  refine ⟨inv (pullback.fst t ι) ≫ pullback.snd t ι, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

end LateralTheory.E.LeafPtWPf
