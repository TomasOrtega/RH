import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.BasePf

/- English proof (translation)
Use `algebraize [f.hom, Polynomial.mapRingHom f.hom]`. Conclude with `(CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip`.
-/
theorem polyPO {A C : CommRingCat.{0}} (f : A ⟶ C) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC C) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact (CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip

/- English proof (translation)
Establish `: (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange` using `RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange`. Conclude with `(RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf`.
-/
theorem et_map {A C : CommRingCat.{0}} (f : A ⟶ C) (hf : Et f) :
    Et (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf

/- English proof (translation)
Introduce `H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo`. Rewrite `hpo` using `[Category.id_comp]`. Establish `hc4 : C4` using `H.2.2.2.2.2.2.2.2.2.2`. Establish `hqB : IsUnit (q : B)` using `by simpa using hq.map c.hom`. Establish `hqY : IsUnit (q : Y')` using `by simpa using hqB.map φ'.hom`.

Establish `sq` using `hpo.flip.paste_horiz (polyPO φ')`. Establish `e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `sq` using `[e1]`.

Establish `hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom))` using `MorphismProperty.le_ind _ _ (et_map c hc)`. Establish `r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom))` using `h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip`. Establish `r1 : RE q i (pC B)` using `hc4 q B hqB i`. Establish `r3 : RE q i (pC Y')` using `hc4 q Y' hqY i`. Establish `e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y'`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `r4 : RE q i (φ' ≫ pC Y')` using `e2 ▸ r1.comp r2`. Conclude with `RE.of_comp_right r3 r4`.
-/
theorem Base_of (h : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial) : LateralTheory.E.t_E3Cut.Base := by
  intro H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo
  rw [Category.id_comp] at hpo
  have hc4 : C4 := H.2.2.2.2.2.2.2.2.2.2
  have hqB : IsUnit (q : B) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqB.map φ'.hom
  have sq := hpo.flip.paste_horiz (polyPO φ')
  have e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom) := by
    ext x; simp
  rw [e1] at sq
  have hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom)) :=
    MorphismProperty.le_ind _ _ (et_map c hc)
  have r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom)) :=
    h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip
  have r1 : RE q i (pC B) := hc4 q B hqB i
  have r3 : RE q i (pC Y') := hc4 q Y' hqY i
  have e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y' := by
    ext x; simp
  have r4 : RE q i (φ' ≫ pC Y') := e2 ▸ r1.comp r2
  exact RE.of_comp_right r3 r4

end LateralTheory.E.BasePf
