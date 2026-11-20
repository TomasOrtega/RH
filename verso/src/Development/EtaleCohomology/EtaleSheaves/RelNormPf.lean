import Development.EtaleCohomology.EtaleSheaves.RelNormPfAff

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

/- English proof (translation)
Introduce `b hb`. Take `⟨p, hm, hp⟩` from `hb`. Take `⟨a', ha'⟩` from `h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩`. Take `⟨a, rfl⟩` from `hs a'`. Conclude with `⟨a, ha'⟩`.
-/
theorem closedAt_comp {X N T : Scheme.{0}} (c' : X ⟶ N) (k' : N ⟶ T) (V : T.Opens)
    (h : ClosedAt c' (k' ⁻¹ᵁ V)) (hs : Function.Surjective (k'.app V)) : ClosedAt (c' ≫ k') V := by
  intro b hb
  obtain ⟨p, hm, hp⟩ := hb
  obtain ⟨a', ha'⟩ := h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩
  obtain ⟨a, rfl⟩ := hs a'
  exact ⟨a, ha'⟩

/- English proof (translation)
Introduce `Z S g _ _ _ V hV`. Establish `H : g = g.toNormalization.toNormalization ≫ (g.toNormalization.fromNormalization ≫ g.fromNormalization)`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, Scheme.Hom.toNormalization_fromNormalization]`. Set `h` to `g.normalizationDesc _ _ H`. Establish `e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization` using `g.toNormalization_normalizationDesc _ _ H`.

Establish `e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization` using `g.normalizationDesc_comp _ _ H`. Establish `i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _` using `Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id]) (by rw [Category.assoc, e2]) (Category.id_comp _)`. Establish `i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _` using `Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id]) (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)`. Establish `: IsIso g.toNormalization.fromNormalization` using `⟨h, i2, i1⟩`. Establish `e` using `g.toNormalization.toNormalization_fromNormalization`.

Rewrite using `[← e]`. Conclude with `closedAt_comp _ _ V (closedAt_preimage _ V hV) (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2`.
-/
theorem normClosed : NormClosed := by
  intro Z S g _ _ _ V hV
  have H : g = g.toNormalization.toNormalization ≫
      (g.toNormalization.fromNormalization ≫ g.fromNormalization) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      Scheme.Hom.toNormalization_fromNormalization]
  let h := g.normalizationDesc _ _ H
  have e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization :=
    g.toNormalization_normalizationDesc _ _ H
  have e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization :=
    g.normalizationDesc_comp _ _ H
  have i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
      (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id])
      (by rw [Category.assoc, e2]) (Category.id_comp _)
  have i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization
      (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id])
      (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)
  have : IsIso g.toNormalization.fromNormalization := ⟨h, i2, i1⟩
  have e := g.toNormalization.toNormalization_fromNormalization
  rw [← e]
  exact closedAt_comp _ _ V (closedAt_preimage _ V hV)
    (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2

/- English proof (translation)
The claim follows from `RelNorm_of_closed normClosed`.
-/
theorem RelNorm_of : LateralTheory.E.SteinPf.RelNorm := RelNorm_of_closed normClosed

end LateralTheory.E.RelNormPf
