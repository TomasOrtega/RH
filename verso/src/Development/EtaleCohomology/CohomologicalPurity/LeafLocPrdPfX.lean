import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Apply `Arrow.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `sch.map _ ≫ sch.map _ = sch.map _`. Rewrite using `[← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]`. Express the relevant statement in the definitionally equal form `sch.map _ ≫ sch.map _ = sch.map _`. Rewrite using `[← Functor.map_comp]`.
-/
theorem opnMap_comp_RLocP {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1`. Establish `e : dbl.map (𝟙 P) = 𝟙 _`. Apply the tactic sequence `apply pushout.hom_ext <;> (simp [dbl.map]; rfl)`. Rewrite using `[e, pull_id]`.
-/
theorem hs_pull_id_RLocP (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    apply pushout.hom_ext <;> (simp [dbl.map]; rfl)
  rw [e, pull_id]

/- English proof (translation)
Introduce `hyp H d P V q _ hq hG`. Establish `a6 : DivisorNaturality` using `hyp.2.2.2.2.1`. Use `haveI := P.cl`. Establish `hcl : IsCl d (fcl d)` using `pick_spec (hCl hyp d)`. Establish `hqA : IsUnit (q : Γ(P.X, V.1))`.

Use `hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom` as an intermediate fact. Simplify using `using this`. Establish `hoff : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B), off B ((P.ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U` using `fun B _ φ => (hZ P.X P.Z P.ι V B φ).2 P.U P.hU`. Establish `e0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U`. Establish `e` using `hoff Γ(P.X, V.1) (RingHom.id _)`.

Rewrite `e` using `[Ideal.map_id]`. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `h0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) ≤ V.2.fromSpec ⁻¹ᵁ P.U` using `le_of_eq e0`. Use `haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec`.

Take `⟨c, hcdef⟩ : ∃ c, c = Hs.pull q (opnMap V.2.fromSpec _ _ h0) _ _ (fcl d q P)` from `⟨_, rfl⟩`. Establish `hc : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B) (x : Fin d → B) hx h, φ.Etale → Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B ((P.ι.ker.ideal V).map φ)) (off _ (P.ι.ker.ideal V)) h) _ _ c = thom d q B ((P.ι.ker.ideal V).map φ) x hx`. Introduce `B _ φ x hx h hφ`. Take `⟨z, hz⟩` from `(hZ P.X P.Z P.ι V B φ).1`. Use `haveI : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ`.

Establish `h' : off B ((P.ι.ker.ideal V).map φ) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U` using `le_of_eq (hoff B φ)`. Rewrite using `[hcdef, ← hs_pull_comp, opnMap_comp_RLocP _ _ _ _ _ _ _ h']`. Conclude with `(hcl q).1 P hq B _ x hx _ z h' inferInstance hz`. Establish `key` using `hPR hyp H d q Γ(P.X, V.1) (P.ι.ker.ideal V) hqA hG.1 hG.2 c hc`. Establish `hU'` using `hoff _ (eta H P V)`.

Take `⟨e, he1, he2⟩` from `hAbv _ P.X (hensTo H P V) _ P.U hU'`. Introduce `n i`. Establish `hh : off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)) ≤ Spec.map (CommRingCat.ofHom (eta H P V)) ⁻¹ᵁ off Γ(P.X, V.1) (P.ι.ker.ideal V)`. Rewrite using `[hoff _ (eta H P V), e0]`. Introduce `x hx`.

Conclude with `hx`. Establish `hk` using `key hh n i`. Establish `hpe : Function.Bijective (Hs.pull q e.hom (n + 2 * d) (i + d))` using `Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv _ _, fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id_RLocP], fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id_RLocP]⟩`. Establish `hcomp : ∀ a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i, Hs.pull q e.hom _ _ (Hs.act q (P` using `abv P.U (sch.map (hensTo H P V))) a (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = Hs.act q (P := opn (off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)))) a (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (eta H P V))) _ _ hh) _ _ …`. Introduce `a`.

Use `(hAN a6 q _ _ e.hom n (2 * d) i d a _).trans ?_` and prove the remaining obligations. Rewrite using `[he1]`. Use `erw [pull_id]`. Rewrite using `[← hs_pull_comp, he2, hcdef, ← hs_pull_comp, opnMap_comp_RLocP]`. Use `(Function.Bijective.of_comp_iff' hpe _).1 ?_` and prove the remaining obligations.

Establish `hf` using `funext hcomp`. Rewrite using `[show (⇑(Hs.pull q e.hom (n + 2 * d) (i + d)) ∘ fun a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i => Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = _ from hf]`. Conclude with `hk`.
-/
theorem LeafLocPrd_of (hCl : LeafCl) (hPR : LeafPrdRing) (hZ : LeafZ) (hAbv : LeafAbv) (hAN : LeafActNat) : LeafLocPrd := by
  intro hyp H d P V q _ hq hG
  have a6 : DivisorNaturality := hyp.2.2.2.2.1
  haveI := P.cl
  have hcl : IsCl d (fcl d) := pick_spec (hCl hyp d)

  have hqA : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have hoff : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B),
      off B ((P.ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
    fun B _ φ => (hZ P.X P.Z P.ι V B φ).2 P.U P.hU
  have e0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
    have e := hoff Γ(P.X, V.1) (RingHom.id _)
    rw [Ideal.map_id] at e
    rw [e]; rfl
  have h0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) ≤ V.2.fromSpec ⁻¹ᵁ P.U := le_of_eq e0
  haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨c, hcdef⟩ : ∃ c, c = Hs.pull q (opnMap V.2.fromSpec _ _ h0) _ _ (fcl d q P) := ⟨_, rfl⟩
  have hc : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B) (x : Fin d → B) hx h, φ.Etale →
      Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B ((P.ι.ker.ideal V).map φ)) (off _ (P.ι.ker.ideal V)) h) _ _ c
        = thom d q B ((P.ι.ker.ideal V).map φ) x hx := by
    intro B _ φ x hx h hφ
    obtain ⟨z, hz⟩ := (hZ P.X P.Z P.ι V B φ).1
    haveI : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    have h' : off B ((P.ι.ker.ideal V).map φ) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
      le_of_eq (hoff B φ)
    rw [hcdef, ← hs_pull_comp, opnMap_comp_RLocP _ _ _ _ _ _ _ h']
    exact (hcl q).1 P hq B _ x hx _ z h' inferInstance hz
  have key := hPR hyp H d q Γ(P.X, V.1) (P.ι.ker.ideal V) hqA hG.1 hG.2 c hc

  have hU' := hoff _ (eta H P V)
  obtain ⟨e, he1, he2⟩ := hAbv _ P.X (hensTo H P V) _ P.U hU'
  intro n i
  have hh : off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)) ≤
      Spec.map (CommRingCat.ofHom (eta H P V)) ⁻¹ᵁ off Γ(P.X, V.1) (P.ι.ker.ideal V) := by
    rw [hoff _ (eta H P V), e0]; intro x hx; exact hx
  have hk := key hh n i
  have hpe : Function.Bijective (Hs.pull q e.hom (n + 2 * d) (i + d)) :=
    Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv _ _,
      fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id_RLocP],
      fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id_RLocP]⟩
  have hcomp : ∀ a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i,
      Hs.pull q e.hom _ _ (Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) =
      Hs.act q (P := opn (off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)))) a
        (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (eta H P V))) _ _ hh) _ _ c) := by
    intro a
    refine (hAN a6 q _ _ e.hom n (2 * d) i d a _).trans ?_
    rw [he1]
    erw [pull_id]
    rw [← hs_pull_comp, he2, hcdef, ← hs_pull_comp, opnMap_comp_RLocP]
  refine (Function.Bijective.of_comp_iff' hpe _).1 ?_
  have hf := funext hcomp
  rw [show (⇑(Hs.pull q e.hom (n + 2 * d) (i + d)) ∘ fun a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i =>
      Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = _ from hf]
  exact hk

end LateralTheory.CohomologicalPurity.TubeCut
