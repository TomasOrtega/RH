import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1`. Establish `e : dbl.map (𝟙 P) = 𝟙 _`. Apply the tactic sequence `apply pushout.hom_ext <;> (simp [dbl.map]; try rfl)`. Rewrite using `[e, pull_id]`.
-/
theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    apply pushout.hom_ext <;> (simp [dbl.map]; try rfl)
  rw [e, pull_id]

/- English proof (translation)
Introduce `n i` and use `Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i, fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id], fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩`.
-/
theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

/- English proof (translation)
Apply `Arrow.hom_ext _ _ _ hr` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `wa` using `Arrow.w α`. Establish `wb` using `Arrow.w β`. Express the relevant statement in the definitionally equal form `α.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ α.right at wa`.

Express the relevant statement in the definitionally equal form `β.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ β.right at wb`. Rewrite `wa` using `[hr]`. Conclude with `wa.trans wb.symm`. Conclude with `congrArg CommaMorphism.left hm`.
-/
theorem abv_ext {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {Q : Arrow Spc} (α β : Q ⟶ abv U π)
    (hr : α.right = β.right) (hm : α ≫ abvMap U π = β ≫ abvMap U π) : α = β := by
  apply Arrow.hom_ext _ _ _ hr
  apply pullback.hom_ext
  · have wa := Arrow.w α
    have wb := Arrow.w β
    change α.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ α.right at wa
    change β.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ β.right at wb
    rw [hr] at wa
    exact wa.trans wb.symm
  · exact congrArg CommaMorphism.left hm

/- English proof (translation)
Apply `Arrow.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `sch.map _ ≫ sch.map _ = sch.map _`. Rewrite using `[← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]`. Express the relevant statement in the definitionally equal form `sch.map _ ≫ sch.map _ = sch.map _`. Rewrite using `[← Functor.map_comp]`.
-/
theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h3 : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h1 ≫ opnMap g U' U h2 = opnMap (f ≫ g) U'' U h3 := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

/- English proof (translation)
Introduce `hyp H d P V q hq hfg h`. Take `⟨a1, -, -, a4, -, -, -, -, b1, -, -, -⟩` from `hyp`. Use `P.cl` as an intermediate fact. Use `set A := Γ(P.X, V.1)`. Use `set I := P.ι.ker.ideal V`.

Use `set φ := eta H P V`. Use `set g := V.2.fromSpec`. Use `set f : Spec (H.obj A I) ⟶ Spec A := Spec.map (CommRingCat.ofHom φ)`. Establish `hqA : IsUnit (q : A)`. Use `hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom` as an intermediate fact.

Simplify using `using this`. Establish `zB` using `(hZ P.X P.Z P.ι V (H.obj A I) φ).2 P.U P.hU`. Establish `zA` using `(hZ P.X P.Z P.ι V A (RingHom.id A)).2 P.U P.hU`. Rewrite `zA` using `[Ideal.map_id]`. Establish `e1 : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ g = g`.

Rewrite using `[show CommRingCat.ofHom (RingHom.id A) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]`. Rewrite `zA` using `[e1]`. Establish `hle : off (H.obj A I) (I.map φ) ≤ f ⁻¹ᵁ (off A I)`. Rewrite using `[zB, zA]`. Introduce `x hx`.

Conclude with `hx`. Establish `ind` using `hI a1 a4 b1 q φ I hfg (H.ind A I) hqA hle`. Take `⟨eA, eAr, eAm⟩` from `hA _ _ g _ P.U zA`. Take `⟨eB, eBr, eBm⟩` from `hA _ _ (f ≫ g) _ P.U zB`. Establish `sq : eB.hom ≫ abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = opnMap f _ _ hle ≫ eA.hom`.

Apply `abv_ext` to reduce the goal to its premises. Rewrite using `[Arrow.comp_right, Arrow.comp_right, eBr, eAr]`. Conclude with `(Category.id_comp (sch.map f)).trans (Category.comp_id (sch.map f)).symm`. Rewrite using `[Category.assoc, Category.assoc, abvRel_abvMap, eBm, eAm, opnMap_comp]`. Establish `e : abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = eB.inv ≫ opnMap f _ _ hle ≫ eA.hom`.

Rewrite using `[Iso.eq_inv_comp, sq]`. Rewrite using `[e]`. Conclude with `exc_comp q (exc_iso q eB.symm) (exc_comp q ind (exc_iso q eA))`.
-/
theorem LeafLocHen_of (hI : LeafIndExc) (hZ : LeafZ) (hA : LeafAbv) : LeafLocHen := by
  intro hyp H d P V q hq hfg h
  obtain ⟨a1, -, -, a4, -, -, -, -, b1, -, -, -⟩ := hyp
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ := eta H P V
  set g := V.2.fromSpec
  set f : Spec (H.obj A I) ⟶ Spec A := Spec.map (CommRingCat.ofHom φ)
  have hqA : IsUnit (q : A) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have zB := (hZ P.X P.Z P.ι V (H.obj A I) φ).2 P.U P.hU
  have zA := (hZ P.X P.Z P.ι V A (RingHom.id A)).2 P.U P.hU
  rw [Ideal.map_id] at zA
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ g = g := by
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  rw [e1] at zA
  have hle : off (H.obj A I) (I.map φ) ≤ f ⁻¹ᵁ (off A I) := by
    rw [zB, zA]; intro x hx; exact hx
  have ind := hI a1 a4 b1 q φ I hfg (H.ind A I) hqA hle
  obtain ⟨eA, eAr, eAm⟩ := hA _ _ g _ P.U zA
  obtain ⟨eB, eBr, eBm⟩ := hA _ _ (f ≫ g) _ P.U zB
  have sq : eB.hom ≫ abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = opnMap f _ _ hle ≫ eA.hom := by
    apply abv_ext
    · rw [Arrow.comp_right, Arrow.comp_right, eBr, eAr]
      exact (Category.id_comp (sch.map f)).trans (Category.comp_id (sch.map f)).symm
    · rw [Category.assoc, Category.assoc, abvRel_abvMap, eBm, eAm, opnMap_comp]
  have e : abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = eB.inv ≫ opnMap f _ _ hle ≫ eA.hom := by
    rw [Iso.eq_inv_comp, sq]
  rw [e]
  exact exc_comp q (exc_iso q eB.symm) (exc_comp q ind (exc_iso q eA))

end LateralTheory.CohomologicalPurity.TubeCut
