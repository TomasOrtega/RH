import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem jGenIso : GenIso := by
  intro O O' k K _ _ _ _ _ _ φ τ h X p
  have hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom τ) ≫ gen O k := by
    simp only [gen, ← Spec.map_comp]
    congr 1
    ext x
    simpa using h x
  refine ⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫
    pullback.congrHom rfl hg ≪≫
    (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

end UpperTheory.Gal.G3

end
