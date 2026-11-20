import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

/- English proof (translation)
Introduce `O O' k K _ _ _ _ _ _ φ τ h X p`. Establish `hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom τ) ≫ gen O k`. Simplify using `only [gen, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `using h x`. Use `⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫ pullback.congrHom rfl hg ≪≫ (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]`. Rewrite using `[pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]`. Simplify using `only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]`.

Rewrite using `[pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]`.
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
