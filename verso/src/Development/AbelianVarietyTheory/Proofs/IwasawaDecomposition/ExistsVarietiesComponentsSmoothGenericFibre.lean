import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyConnectedOfAlgClosedInFunctionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.GenFibreComp

/- English proof (translation)
Establish `hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V` using `hg ▸ specializes_rfl`. Use `⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩` and prove the remaining obligations. Establish `h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom`. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]`. Conclude with `congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans (Category.id_comp _))`.

Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom = CommRingCat.ofHom ψ`. Rewrite using `[← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Rewrite `h2` using `[← h1]`. Use extensionality with `a`. Establish `h3` using `congrArg (fun t => t.hom a) h2`.

Use `Eq.trans ?_ h3` and prove the remaining obligations. Establish `h4 : p.appLE ⊤ ⊤ le_top = p.appTop`. Simplify using `only [Scheme.Hom.appLE, Scheme.Hom.appTop]`. Conclude with `(congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)`. Rewrite using `[← h4]`.

Both sides reduce to the same expression.
-/
theorem exists_fn_hom {F L : Type} [Field F] [Field L] {V : Scheme.{0}} [IsIntegral V] (p : V ⟶ Sp F)
    (g : Sp L ⟶ V) (hg : g (IsLocalRing.closedPoint L) = genericPoint V) (ψ : F →+* L) (hψ : g ≫ p = spMap ψ) :
    ∃ φ : V.functionField →+* L, φ.comp (GlobalTheory.Cartier.constFn p) = ψ := by
  have hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V := hg ▸ specializes_rfl
  refine ⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩
  have h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g
      = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
    exact congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans
      (Category.id_comp _))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = CommRingCat.ofHom ψ := by
    rw [← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h1] at h2
  ext a
  have h3 := congrArg (fun t => t.hom a) h2
  refine Eq.trans ?_ h3
  have h4 : p.appLE ⊤ ⊤ le_top = p.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [← h4]
  rfl

/- English proof (translation)
Establish `hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Simplify using the standard rewrite rules. Establish `hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Simplify using the standard rewrite rules. Establish `: IsIso (spMap e.symm.toRingHom)` using `⟨_, hi, hi'⟩`. Establish `h1` using `(GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h`. Establish `h2` using `(GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _ inferInstance h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]`.
-/
theorem isProjOver_comp_equiv {F K : Type} [Field F] [Field K] (e : F ≃+* K) {X : Scheme.{0}} (p : X ⟶ Sp K)
    (h : IsProjOver p) : IsProjOver (p ≫ spMap e.toRingHom) := by
  have hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have : IsIso (spMap e.symm.toRingHom) := ⟨_, hi, hi'⟩
  have h1 := (GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h
  have h2 := (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _
    inferInstance h1
  convert h2 using 1
  rw [IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm`. Establish `hS : Smooth (genStr Z)` using `SmoothOfRelativeDimension.smooth Dw.dim _`. Use `isProper_genStr Z` as an intermediate fact. Establish `: IsLocallyNoetherian (gen Z)` using `LocallyOfFiniteType.isLocallyNoetherian (genStr Z)`. Establish `: CompactSpace (gen Z)` using `QuasiCompact.compactSpace_of_compactSpace (genStr Z)`.

Establish `: IsNoetherian (gen Z)` using `{}`. Use `Z.jQ_open` as an intermediate fact. Establish `hcc` using `fun z : gen Z => PtComp.connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z`. Establish `hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1` using `fun i => CompSplitPfD.cspD_gen i.2`. Establish `hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1` using `fun i => by`.

Assume the negation of the conclusion as `hn`. Conclude with `Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h)) mem_connectedComponent (hgen i).mem`. Set `V : Comp Xo c → (gen Z).Opens` to `fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩`. Establish `hred : IsReduced (gen Z)`. Use `GlobalTheory.isNormalScheme_of_smooth (genStr Z)` as an intermediate fact.

Conclude with `GlobalTheory.IsNormalScheme.isReduced`. Establish `: CharZero F` using `e.toRingHom.charZero`. Establish `: IsIso (spMap e.toRingHom)` using `inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))`. Establish `hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom)` using `isProjOver_comp_equiv e _ ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)`. Establish `key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧ ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom` using `fun i => by`.

Establish `: IrreducibleSpace (V i).toScheme` using `Subtype.irreducibleSpace (hcc _).1.1`. Establish `: IsIntegral (V i).toScheme` using `isIntegral_of_irreducibleSpace_of_isReduced _`. Establish `hcl : IsClosedImmersion (V i).ι` using `IsClosedImmersion.of_isPreimmersion _ (by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `isClosed_connectedComponent)`.

Establish `hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)` using `(GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj`. Establish `hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)`. Establish `h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)` using `inferInstance`. Simplify using `using h`. Establish `hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι`.

Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]`. Conclude with `mem_connectedComponent`. Set `g : Sp (kap i) ⟶ (V i).toScheme` to `IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr`. Establish `hg : g ≫ (V i).ι = genSp i ≫ Z.jQ` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i)`. Conclude with `(Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))`. Establish `hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme`. Establish `h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i)` using `hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous`. Take `⟨a, ha⟩` from `h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩`.

Establish `h2 : a = genPt i` using `CompSplitPfD.cspD_max i.2 (hgen i) a (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))`. Apply `(V i).ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hgp, ← ha, h2]`. Take `⟨φ, hφ⟩` from `exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg ((algebraMap c.F (kap i)).comp e.toRingHom) (by`. Rewrite using `[reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]`.

Conclude with `(congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)`. Establish `: GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)`. Use `GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_` and prove the remaining obligations. Introduce and unpack `a ⟨P, hP, hPa⟩`. Set `χ : (V i).toScheme.functionField →+* Om i` to `(algebraMap (kap i) (Om i)).comp φ`.

Establish `hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) = (algebraMap c.F (Om i)).comp e.toRingHom`. Rewrite using `[RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]`. Take `⟨b, hb⟩` from `hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩`. Use `⟨e.symm b, χ.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← hb]`. Conclude with `(RingHom.congr_fun hχ _).trans (by simp)`. Conclude with `GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp`. Use `choose B ε hd hs using key`. Establish `hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i))` using `fun i => by`.

Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ, Scheme.Opens.range_ι]`. Both sides reduce to the same expression. Use `⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hs, Iso.inv_hom_id_assoc]`. Rewrite using `[hrange]`.

Rewrite `hp` using `[← hpre]`. Conclude with `hp`. Use `⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hrange]`.

Establish `h` using `(hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem`. Rewrite using `[← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]`. Conclude with `mem_connectedComponent`. Use `beta_reduce at hi`. Rewrite `hi` using `[hrange]`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hpre, connectedComponent_eq hi]`.
-/
theorem exists_vars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1 := fun i => CompSplitPfD.cspD_gen i.2
  have hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1 := fun i => by
    by_contra hn
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _
      ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h))
      mem_connectedComponent (hgen i).mem
  let V : Comp Xo c → (gen Z).Opens := fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧
      ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom := fun i => by
    have : IrreducibleSpace (V i).toScheme := Subtype.irreducibleSpace (hcc _).1.1
    have : IsIntegral (V i).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hcl : IsClosedImmersion (V i).ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
    have hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) :=
      (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
    have hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
      simpa using h
    have hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]
      exact mem_connectedComponent
    let g : Sp (kap i) ⟶ (V i).toScheme := IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr
    have hg : g ≫ (V i).ι = genSp i ≫ Z.jQ := IsOpenImmersion.lift_fac _ _ _
    have hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i) := by
      exact (Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))
    have hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme := by
      have h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i) :=
        hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous
      obtain ⟨a, ha⟩ := h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
      have h2 : a = genPt i := CompSplitPfD.cspD_max i.2 (hgen i) a
        (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))
      apply (V i).ι.isOpenEmbedding.injective
      rw [hgp, ← ha, h2]
    obtain ⟨φ, hφ⟩ := exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg
      ((algebraMap c.F (kap i)).comp e.toRingHom) (by
        rw [reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]
        exact (congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)
    have : GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
      rintro a ⟨P, hP, hPa⟩
      let χ : (V i).toScheme.functionField →+* Om i := (algebraMap (kap i) (Om i)).comp φ
      have hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) =
          (algebraMap c.F (Om i)).comp e.toRingHom := by
        rw [RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]
      obtain ⟨b, hb⟩ := hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩
      refine ⟨e.symm b, χ.injective ?_⟩
      rw [← hb]
      exact (RingHom.congr_fun hχ _).trans (by simp)
    exact GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  choose B ε hd hs using key
  have hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i)) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  refine ⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [hrange]
    rw [← hpre] at hp
    exact hp
  · refine ⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩
    · beta_reduce
      rw [hrange]
      have h := (hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem
      rw [← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]
      exact mem_connectedComponent
    · beta_reduce at hi
      rw [hrange] at hi
      apply Subtype.ext
      rw [← hpre, connectedComponent_eq hi]

end GlobalTheory.GenFibreComp
