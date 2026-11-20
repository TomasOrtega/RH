import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Geo.Cut.fEtCut :
    UpperTheory.Gal.Int.Geo.Cut.FEtCut := by
  intro Y' Y T' T j s t i s' t' d hj hr hst hs
  haveI := hj.op
  haveI := hr.op
  have hpre : s ⁻¹ᵁ j.opensRange = i.opensRange := by
    apply SetLike.coe_injective
    change s ⁻¹' Set.range j = Set.range i
    rw [hr.rng]
    ext x
    exact ⟨fun h => ⟨h, hst x h⟩, fun h => h.1⟩
  have pb : IsPullback s' i j s := IsOpenImmersion.isPullback s' i j s hr.es.symm hpre
  obtain ⟨hfin, het, hcard⟩ := hs
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) pb.flip hfin,
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) pb.flip het, ?_⟩
  intro K _ _ x
  rw [← hcard K (x ≫ j)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ i, by rw [Category.assoc, ← pb.w, ← Category.assoc, y.2]⟩
      invFun := fun z => ⟨pb.lift x z.1 z.2.symm, pb.lift_fst _ _ _⟩
      left_inv := fun y => Subtype.ext (pb.hom_ext (by simp [y.2]) (by simp))
      right_inv := fun z => Subtype.ext (pb.lift_snd _ _ _) }
