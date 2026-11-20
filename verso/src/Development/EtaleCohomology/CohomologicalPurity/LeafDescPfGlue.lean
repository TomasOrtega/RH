import Development.EtaleCohomology.CohomologicalPurity.LeafDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Substitute `hV hk` using the available equality. Introduce `w hw`. Conclude with `hW hw`.
-/
theorem le_of_comp {Y Z X : Scheme.{0}} {W : Y.Opens} {V : Z.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (k : Y ⟶ X) (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ V := by
  subst hV hk; intro w hw; exact hW hw

/- English proof (translation)
Substitute `hV` using the available equality. Use `ext`. Both sides reduce to the same expression.
-/
theorem pre_comp {Y Z X : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ X) (V : Z.Opens) (U : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V = (f ≫ g) ⁻¹ᵁ U := by
  subst hV; ext; rfl

/- English proof (translation)
Introduce `q X U m i hG A p s hcov H`. Set `E` to `fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)`. Take `⟨c, hc⟩` from `hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by`. Introduce `a b x hxa hxb hxU`. Take `⟨y, rfl⟩ : x ∈ Set.range (p a).j` from `hxa`.

Take `⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩` from `H a b y hxU hxb`. Set `P : Pc U` to `⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩`. Establish `ha : P.j.opensRange ≤ (p a).j.opensRange` using `by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩`. Establish `hb : P.j.opensRange ≤ (p b).j.opensRange`. Introduce and unpack `_ ⟨w, rfl⟩`.

Use `⟨u w, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(u ≫ (p b).j) w = (t.j ≫ (p a).j) w`. Rewrite using `[hcomm]`. Establish `ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom`. Rewrite using `[← cancel_mono ((p a).j.opensRange.ι)]`.

Simplify using `only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]`. Both sides reduce to the same expression. Establish `eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom`. Rewrite using `[← cancel_mono ((p b).j.opensRange.ι)]`. Simplify using `only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]`.

Conclude with `hcomm`. Establish `hPV : P.V ≤ P.j ⁻¹ᵁ U` using `P.hV.le`. Establish `ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U)` using `le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl`. Establish `hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U)` using `le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl`. Use `⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩` and prove the remaining obligations.

Apply `(pc_bij P m i).1` to reduce the goal to its premises. Establish `k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U)` using `le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV`. Establish `k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U)` using `le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV`. Rewrite using `[pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2, ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]`. Express the relevant statement in the definitionally equal form `Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))`.

Rewrite using `[Equiv.apply_symm_apply, Equiv.apply_symm_apply]`. Conclude with `heq)`. Use `⟨c, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[pc_res, hc a]`. Conclude with `(E a).apply_symm_apply (s a)`.
-/
theorem LeafPcGlue_pf : LeafPcGlue := by
  intro q X U m i hG A p s hcov H
  let E := fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)
  obtain ⟨c, hc⟩ := hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by
    intro a b x hxa hxb hxU
    obtain ⟨y, rfl⟩ : x ∈ Set.range (p a).j := hxa
    obtain ⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩ := H a b y hxU hxb
    let P : Pc U := ⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩
    have ha : P.j.opensRange ≤ (p a).j.opensRange := by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩
    have hb : P.j.opensRange ≤ (p b).j.opensRange := by
      rintro _ ⟨w, rfl⟩
      refine ⟨u w, ?_⟩
      change (u ≫ (p b).j) w = (t.j ≫ (p a).j) w
      rw [hcomm]
    have ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p a).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]; rfl
    have eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p b).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
      exact hcomm
    have hPV : P.V ≤ P.j ⁻¹ᵁ U := P.hV.le
    have ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    have hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    refine ⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩
    apply (pc_bij P m i).1
    have k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV
    have k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV
    rw [pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2,
      ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]
    change Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact heq)
  refine ⟨c, fun a => ?_⟩
  rw [pc_res, hc a]
  exact (E a).apply_symm_apply (s a)

/- English proof (translation)
The claim follows from `LeafDesc_of hD hF hS hG LeafPcGlue_pf`.
-/
theorem LeafDesc_of' (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) : LeafDesc :=
  LeafDesc_of hD hF hS hG LeafPcGlue_pf

end LateralTheory.CohomologicalPurity.Cl
