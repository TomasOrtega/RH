import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

/- English proof (translation)
Set `d : Derivation k A K` to `(Algebra.linearMap A K).compDer D`. Set `f : Ω[A⁄k] →ₗ[A] K` to `d.liftKaehlerDifferential`. Establish `hb` using `KaehlerDifferential.isBaseChange_of_formallyEtale k A K`. Set `g : Ω[K⁄k] →ₗ[K] K` to `hb.lift f`. Use `⟨g.compDer (KaehlerDifferential.D k K), fun a => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g (KaehlerDifferential.D k K (algebraMap A K a)) = _`. Rewrite using `[← KaehlerDifferential.map_D k k A K]`. Use `erw [hb.lift_eq]`. Simplify using `[f, d]`.
-/
theorem exists_derivation_extend {k A K : Type} [CommRing k] [CommRing A] [CommRing K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [Algebra.FormallyEtale A K] (D : Derivation k A A) :
    ∃ D' : Derivation k K K, ∀ a, D' (algebraMap A K a) = algebraMap A K (D a) := by
  let d : Derivation k A K := (Algebra.linearMap A K).compDer D
  let f : Ω[A⁄k] →ₗ[A] K := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale k A K
  let g : Ω[K⁄k] →ₗ[K] K := hb.lift f
  refine ⟨g.compDer (KaehlerDifferential.D k K), fun a => ?_⟩
  change g (KaehlerDifferential.D k K (algebraMap A K a)) = _
  rw [← KaehlerDifferential.map_D k k A K]
  erw [hb.lift_eq]
  simp [f, d]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

/- English proof (translation)
Rewrite using `[Scheme.Hom.germ_stalkMap_apply f V x hfx y, Scheme.Hom.appLE]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]`.
-/
theorem germ_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) (U' : X.Opens) (e : U' ≤ f ⁻¹ᵁ V) (x : X)
    (hx : x ∈ U') (hfx : f x ∈ V) (y : Γ(Y, V)) :
    X.presheaf.germ U' x hx (f.appLE V U' e y) = f.stalkMap x (Y.presheaf.germ V (f x) hfx y) := by
  rw [Scheme.Hom.germ_stalkMap_apply f V x hfx y, Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

def derivOfConst {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (D : Derivation ℤ A A)
    (hD : ∀ a, D (φ a) = 0) : (letI := φ.toAlgebra; Derivation k A A) :=
  letI := φ.toAlgebra
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun a x => by
      rw [Algebra.smul_def, D.leibniz, RingHom.algebraMap_toAlgebra, hD, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c TF Z _ U hU ρ hρ N Dl`. Use `set W := barComp TF.Y Z with hW`. Use `set η₀ := genericPoint (X₀ TF.Y Z) with hη₀`. Establish `hη : W.ι η₀ ∈ U.1`. Establish `e` using `congrArg (fun f : Sp (X₀ TF.Y Z).functionField ⟶ TF.Y.X => f (IsLocalRing.closedPoint _)) hρ`.

Simplify using `only [Scheme.Hom.comp_apply] at e`. Use `show W.ι η₀ ∈ (U.1 : Set TF.Y.X)`. Rewrite using `[← U.2.range_fromSpec]`. Use `⟨_, e.trans ?_⟩` and prove the remaining obligations. Conclude with `congrArg W.ι Scheme.fromSpecStalk_closedPoint`.

Establish `hmono : Mono (LogKS.chart U)` using `by haveI := U.2.isOpenImmersion_fromSpec`. Unfold `LogKS.chart`. Use `infer_instance`. Establish `hρ' : ρ = (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom`. Establish `e : CommRingCat.ofHom ρ = TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀`.

Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (LogKS.chart U)]`. Use `hρ.trans ?_` and prove the remaining obligations. Establish `e1` using `U.2.fromSpecStalk_eq_fromSpecStalk hη`. Rewrite using `[Spec.map_comp, Category.assoc, LogKS.chart]`.

Use `show (X₀ TF.Y Z).fromSpecStalk η₀ ≫ W.ι = _`. Rewrite using `[← Scheme.SpecMap_stalkMap_fromSpecStalk, ← e1]`. Both sides reduce to the same expression. Conclude with `congrArg CommRingCat.Hom.hom e`. Substitute `hρ'` using the available equality.

Establish `hiso : IsIso (W.ι.stalkMap η₀)` using `inferInstance`. Use `letI iA : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra`. Use `letI iK : Algebra c.F (X₀ TF.Y Z).functionField := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra`. Use `letI iAK : Algebra Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom.toAlgebra`. Establish `htow : IsScalarTower c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField`.

Use `IsScalarTower.of_algebraMap_eq' ?_` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, GlobalTheory.Cartier.constFn, GlobalTheory.Cartier.fnOf, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, CommRingCat.hom_comp]`. Use `(germ_appLE_apply (s₀ TF.Y Z) ⊤ ⊤ _ (genericPoint (X₀ TF.Y Z)) trivial trivial _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (W.ι.stalkMap η₀).hom (germ_appLE_apply TF.Y.s ⊤ U.1 _ (W.ι η₀) hη trivial _)).symm` and prove the remaining obligations.

Rewrite using `[show s₀ TF.Y Z = W.ι ≫ TF.Y.s from rfl, Scheme.Hom.stalkMap_comp]`. Both sides reduce to the same expression. Use `letI iS : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk (W.ι η₀)) := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (U := U.1) ⟨W.ι η₀, hη⟩`. Establish `hloc` using `U.2.isLocalization_stalk ⟨W.ι η₀, hη⟩`. Set `eK : TF.Y.X.presheaf.stalk (W.ι η₀) ≃ₐ[Γ(TF.Y.X, U.1)] (X₀ TF.Y Z).functionField` to `AlgEquiv.ofRingEquiv (f := (asIso (W.ι.stalkMap η₀)).commRingCatIsoToRingEquiv) fun _ => rfl`.

Use `haveI := IsLocalization.isLocalization_of_algEquiv (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl eK`. Use `haveI : Algebra.FormallyEtale Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl`. Use `choose D hD using fun j => exists_derivation_extend (k := c.F) (K := (X₀ TF.Y Z).functionField) (derivOfConst (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1) (Dl j).1 (Dl j).2.1)`. Conclude with `⟨D, fun j r => hD j r⟩`.
-/
theorem exists_genDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U hU ρ hρ N Dl
  set W := barComp TF.Y Z with hW
  set η₀ := genericPoint (X₀ TF.Y Z) with hη₀
  have hη : W.ι η₀ ∈ U.1 := by
    have e := congrArg (fun f : Sp (X₀ TF.Y Z).functionField ⟶ TF.Y.X => f (IsLocalRing.closedPoint _)) hρ
    simp only [Scheme.Hom.comp_apply] at e
    show W.ι η₀ ∈ (U.1 : Set TF.Y.X)
    rw [← U.2.range_fromSpec]
    refine ⟨_, e.trans ?_⟩
    exact congrArg W.ι Scheme.fromSpecStalk_closedPoint
  have hmono : Mono (LogKS.chart U) := by
    haveI := U.2.isOpenImmersion_fromSpec
    unfold LogKS.chart; infer_instance
  have hρ' : ρ = (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom := by
    have e : CommRingCat.ofHom ρ = TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀ := by
      apply Spec.map_injective
      rw [← cancel_mono (LogKS.chart U)]
      refine hρ.trans ?_
      have e1 := U.2.fromSpecStalk_eq_fromSpecStalk hη
      rw [Spec.map_comp, Category.assoc, LogKS.chart]
      show (X₀ TF.Y Z).fromSpecStalk η₀ ≫ W.ι = _
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← e1]
      rfl
    exact congrArg CommRingCat.Hom.hom e
  subst hρ'
  have hiso : IsIso (W.ι.stalkMap η₀) := inferInstance
  letI iA : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  letI iK : Algebra c.F (X₀ TF.Y Z).functionField := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI iAK : Algebra Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom.toAlgebra
  have htow : IsScalarTower c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, GlobalTheory.Cartier.constFn, GlobalTheory.Cartier.fnOf,
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, CommRingCat.hom_comp]
    refine (germ_appLE_apply (s₀ TF.Y Z) ⊤ ⊤ _ (genericPoint (X₀ TF.Y Z)) trivial trivial _).trans ?_
    refine Eq.trans ?_ (congrArg (W.ι.stalkMap η₀).hom
      (germ_appLE_apply TF.Y.s ⊤ U.1 _ (W.ι η₀) hη trivial _)).symm
    rw [show s₀ TF.Y Z = W.ι ≫ TF.Y.s from rfl, Scheme.Hom.stalkMap_comp]
    rfl
  letI iS : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk (W.ι η₀)) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (U := U.1) ⟨W.ι η₀, hη⟩
  have hloc := U.2.isLocalization_stalk ⟨W.ι η₀, hη⟩
  let eK : TF.Y.X.presheaf.stalk (W.ι η₀) ≃ₐ[Γ(TF.Y.X, U.1)] (X₀ TF.Y Z).functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso (W.ι.stalkMap η₀)).commRingCatIsoToRingEquiv) fun _ => rfl
  haveI := IsLocalization.isLocalization_of_algEquiv (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl eK
  haveI : Algebra.FormallyEtale Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl
  choose D hD using fun j => exists_derivation_extend (k := c.F) (K := (X₀ TF.Y Z).functionField)
    (derivOfConst (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1) (Dl j).1 (Dl j).2.1)
  exact ⟨D, fun j r => hD j r⟩

end GlobalTheory.LogKSDiv
