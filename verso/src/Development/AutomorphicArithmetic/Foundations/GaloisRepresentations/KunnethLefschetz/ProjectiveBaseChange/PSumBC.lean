import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Establish `e` using `h.isoPullback_hom_fst`. Rewrite using `[← e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr (fun y => ⟨h.isoPullback.inv y, by simp⟩), Set.image_univ, Scheme.Pullback.range_fst]`.
-/
private theorem range_eq_preimage {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  have e := h.isoPullback_hom_fst
  rw [← e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (fun y => ⟨h.isoPullback.inv y, by simp⟩), Set.image_univ,
    Scheme.Pullback.range_fst]

/- English proof (translation)
Unfold `UpperTheory.Gal.KunnethLefschetz.SumBC`. Introduce `X' X r Y' Y j' j f u h hj`. Take `⟨ho, hc, hd⟩` from `hj`. Use `⟨fun s => ?_, fun x => ?_, fun s s' hs => ?_⟩` and prove the remaining obligations. Use `ho s` as an intermediate fact.

Conclude with `MorphismProperty.of_isPullback (P := @IsOpenImmersion) (h s).flip (ho s)`. Take `⟨s, hs⟩` from `hc (f x)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[range_eq_preimage (h s)]`. Conclude with `hs`.

Rewrite using `[range_eq_preimage (h s), range_eq_preimage (h s')]`. Conclude with `(hd s s' hs).preimage f`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.sumBC_holds :
    UpperTheory.Gal.KunnethLefschetz.SumBC := by
  unfold UpperTheory.Gal.KunnethLefschetz.SumBC
  intro X' X r Y' Y j' j f u h hj
  obtain ⟨ho, hc, hd⟩ := hj
  refine ⟨fun s => ?_, fun x => ?_, fun s s' hs => ?_⟩
  · have := ho s
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (h s).flip (ho s)
  · obtain ⟨s, hs⟩ := hc (f x)
    refine ⟨s, ?_⟩
    rw [range_eq_preimage (h s)]
    exact hs
  · rw [range_eq_preimage (h s), range_eq_preimage (h s')]
    exact (hd s s' hs).preimage f
