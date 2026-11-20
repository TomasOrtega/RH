import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `h : Scheme.Hom.appTop (f ≫ g) = Scheme.Hom.appTop g ≫ Scheme.Hom.appTop f`. Simplify using `[Scheme.Hom.appTop]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private theorem appTop_comp_hom_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (f ≫ g))) s
      = (ConcreteCategory.hom (Scheme.Hom.appTop f))
        ((ConcreteCategory.hom (Scheme.Hom.appTop g)) s) := by
  have h : Scheme.Hom.appTop (f ≫ g) = Scheme.Hom.appTop g ≫ Scheme.Hom.appTop f := by
    simp [Scheme.Hom.appTop]
  rw [h]
  rfl

/- English proof (translation)
Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec]`. Introduce `i`. Take `⟨a⟩` from `i`. Use `show (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q))) (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)) = (ConcreteCategory.hom (Scheme.Hom.appTop (D.ι ≫ projLeft k M n))) (AffineSpace.coord (Spec (CommRingCat.of …`.

Rewrite using `[appTop_comp_hom_apply, appTop_comp_hom_apply, projLeft_appTop_coord, projLeft_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inl]`.
-/
theorem graphMorphismToAffineSpace_comp_projLeft (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q = D.ι ≫ projLeft k M n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec]
  · intro i
    obtain ⟨a⟩ := i
    show (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = (ConcreteCategory.hom (Scheme.Hom.appTop (D.ι ≫ projLeft k M n)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
    rw [appTop_comp_hom_apply, appTop_comp_hom_apply, projLeft_appTop_coord, projLeft_appTop_coord,
      graphMorphismToAffineSpace_appTop_coord_inl]

/- English proof (translation)
Establish `hsq : f ≫ i = 𝟙 X ≫ (f ≫ i)` using `by simp`. Establish `hp : IsPullback f (𝟙 X) i (f ≫ i)`. Use `IsPullback.of_isLimit (c := Limits.PullbackCone.mk f (𝟙 X) hsq) ?_` and prove the remaining obligations. Use `Limits.PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)` and prove the remaining obligations. Establish `hc : s.fst ≫ i = (s.snd ≫ f) ≫ i`.

Rewrite using `[Category.assoc]`. Conclude with `s.condition`. Conclude with `((cancel_mono i).mp hc).symm`. Simplify using the standard rewrite rules. Simplify using `using h₂`.

Conclude with `MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip h`.
-/
private theorem smooth_of_smooth_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Y ⟶ Z) [IsOpenImmersion i] (h : Smooth (f ≫ i)) : Smooth f := by
  have hsq : f ≫ i = 𝟙 X ≫ (f ≫ i) := by simp
  have hp : IsPullback f (𝟙 X) i (f ≫ i) := by
    refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk f (𝟙 X) hsq) ?_
    refine Limits.PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
      (fun s m h₁ h₂ => ?_)
    · have hc : s.fst ≫ i = (s.snd ≫ f) ≫ i := by
        rw [Category.assoc]; exact s.condition
      exact ((cancel_mono i).mp hc).symm
    · simp
    · simpa using h₂
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip h

/- English proof (translation)
Establish `hinj : Function.Injective ⇑((I.subschemeObjIso V).inv.hom)`. Introduce `a b hab`. Establish `h1 : ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom a = ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom b`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]`. Simplify using `using h1`.

Rewrite using `[Scheme.IdealSheafData.subschemeι_app]`. Use extensionality with `x`. Simplify using `only [CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]`. Rewrite using `[← map_zero ((I.subschemeObjIso V).inv.hom), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]`.
-/
private theorem ker_subschemeι_app {Z : Scheme.{u}} (I : Z.IdealSheafData)
    (V : Z.affineOpens) :
    RingHom.ker (Scheme.Hom.app I.subschemeι (V : Z.Opens)).hom = I.ideal V := by
  have hinj : Function.Injective ⇑((I.subschemeObjIso V).inv.hom) := by
    intro a b hab
    have h1 : ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom a
        = ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom b := by
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]
    simpa using h1
  rw [Scheme.IdealSheafData.subschemeι_app]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  rw [← map_zero ((I.subschemeObjIso V).inv.hom), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Establish `h` using `(Scheme.IdealSheafData.equivOfIsAffine (X := Z)).apply_symm_apply J`. Rewrite `h` using `[Scheme.IdealSheafData.equivOfIsAffine_symm_apply, Scheme.IdealSheafData.equivOfIsAffine_apply]`. Conclude with `h`.
-/
private theorem ideal_top_ofIdealTop_eq {Z : Scheme.{u}} [IsAffine Z]
    (J : Ideal Γ(Z, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    Scheme.IdealSheafData.equivOfIsAffine_apply] at h
  exact h

/- English proof (translation)
Establish `hI` using `(Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply I`. Establish `hJ` using `(Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply J`. Rewrite `hI`, `hJ` using `[Scheme.IdealSheafData.equivOfIsAffine_apply, Scheme.IdealSheafData.equivOfIsAffine_symm_apply]`. Rewrite using `[← hI, ← hJ, h]`.
-/
private theorem eq_of_ideal_top_eq {Z : Scheme.{u}} [IsAffine Z] {I J : Z.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top Z⟩ = J.ideal ⟨⊤, isAffineOpen_top Z⟩) : I = J := by
  have hI := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply I
  have hJ := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply,
    Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at hI hJ
  rw [← hI, ← hJ, h]

/- English proof (translation)
Use `eq_of_ideal_top_eq ?_` and prove the remaining obligations. Simplify using `only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, ideal_top_ofIdealTop_eq]`.
-/
private theorem ofIdealTop_sup {Z : Scheme.{u}} [IsAffine Z] (I J : Ideal Γ(Z, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  refine eq_of_ideal_top_eq ?_
  simp only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, ideal_top_ofIdealTop_eq]

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span]`.
-/
private theorem comap_ofIdealTop_span {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (s : Set Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span s)).comap f =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop f)) '' s)) := by
  rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span]

/- English proof (translation)
Rewrite using `[coordSubspaceIdeal_eq_ofIdealTop_span_coord, Finset.coe_univ, Set.image_univ]`.
-/
private theorem coordSubspaceIdeal_univ_eq_ofIdealTop (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m Finset.univ =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (fun i : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)))) := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Finset.coe_univ, Set.image_univ]

/- English proof (translation)
Establish `: IsIso (Scheme.Hom.toImage f)` using `inferInstance`. Establish `hc : Scheme.Hom.toImage f ≫ (Scheme.Hom.ker f).subschemeι = f` using `Scheme.Hom.toImage_imageι f`. Establish `h2 : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop (inv (Scheme.Hom.toImage f)))) ((CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) z) = z`. Introduce `z`. Establish `hz` using `(appTop_comp_hom_apply (inv (Scheme.Hom.toImage f)) (Scheme.Hom.toImage f) z).symm`.

Rewrite `hz` using `[IsIso.inv_hom_id]`. Simplify using `using hz`. Establish `hinj : Function.Injective ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f)))`. Introduce `a b hab`. Establish `ha` using `h2 a`.

Rewrite `ha` using `[hab, h2 b]`. Conclude with `ha.symm`. Establish `happ : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) z = (CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) ((CommRingCat.Hom.hom (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) z)`. Introduce `z`. Use `conv_lhs => rw [← hc]`.

Rewrite using `[appTop_comp_hom_apply]`. Establish `hkers : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) = RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι)))`. Use extensionality with `z`. Simplify using `only [RingHom.mem_ker]`. Rewrite using `[happ z]`.

Prove the components needed by the constructor for the conclusion. Introduce `hz`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hz, map_zero]`. Introduce `hz`.

Rewrite using `[hz, map_zero]`. Use `eq_of_ideal_top_eq ?_` and prove the remaining obligations. Rewrite using `[ideal_top_ofIdealTop_eq, ← ker_subschemeι_app (Scheme.Hom.ker f) ⟨⊤, isAffineOpen_top Y⟩]`. Conclude with `hkers.symm`.
-/
private theorem ker_eq_ofIdealTop_ker_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    Scheme.Hom.ker f =
      Scheme.IdealSheafData.ofIdealTop
        (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f))) := by
  have : IsIso (Scheme.Hom.toImage f) := inferInstance
  have hc : Scheme.Hom.toImage f ≫ (Scheme.Hom.ker f).subschemeι = f :=
    Scheme.Hom.toImage_imageι f
  have h2 : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop (inv (Scheme.Hom.toImage f))))
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) z) = z := by
    intro z
    have hz := (appTop_comp_hom_apply (inv (Scheme.Hom.toImage f))
      (Scheme.Hom.toImage f) z).symm
    rw [IsIso.inv_hom_id] at hz
    simpa using hz
  have hinj : Function.Injective
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) := by
    intro a b hab
    have ha := h2 a
    rw [hab, h2 b] at ha
    exact ha.symm
  have happ : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) z
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f)))
        ((CommRingCat.Hom.hom (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) z) := by
    intro z
    conv_lhs => rw [← hc]
    rw [appTop_comp_hom_apply]
  have hkers : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) =
      RingHom.ker (CommRingCat.Hom.hom
        (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) := by
    ext z
    simp only [RingHom.mem_ker]
    rw [happ z]
    constructor
    · intro hz
      apply hinj
      rw [hz, map_zero]
    · intro hz
      rw [hz, map_zero]
  refine eq_of_ideal_top_eq ?_
  rw [ideal_top_ofIdealTop_eq,
    ← ker_subschemeι_app (Scheme.Hom.ker f) ⟨⊤, isAffineOpen_top Y⟩]
  exact hkers.symm

/- English proof (translation)
Establish `h1 : ∀ i : ULift.{u, 0} (Fin (c + q)), (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom)) (AffineSpace.coord (Spec (CommRingCat.of k)) i) = AffineSpace.coord (Spec (CommRingCat.of k)) ((uliftFinSumEquiv.{u} c …`. Introduce `i`. Simplify using `[affineSpaceIsoOfEquiv]`. Establish `h2 : ∀ a : Fin c, (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q))) (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)) = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inl a) : ULift.{u, 0} (Fin c ⊕ Fin q))`. Introduce `a`.

Simplify using the standard rewrite rules. Establish `h3 : ∀ b : Fin q, (CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q))) (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b)) = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inr b) : ULift.{u, 0} (Fin c ⊕ Fin q))`. Introduce `b`. Simplify using the standard rewrite rules. Establish `hset : ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom)) '' Set.range (fun i : Fin (c + q) => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) = (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (pr …`.

Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_range, Set.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨i, rfl⟩, rfl⟩`. Rewrite using `[h1]`.

Break down `hcase : ((uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)).down with a | b` into its components or cases. Use `Or.inl ⟨_, ⟨a, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Establish `hEq : ULift.up.{u, 0} (Sum.inl a : Fin c ⊕ Fin q) = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)`. Rewrite using `[← hcase]`.

Rewrite using `[hEq]`. Use `Or.inr ⟨_, ⟨b, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Establish `hEq : ULift.up.{u, 0} (Sum.inr b : Fin c ⊕ Fin q) = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)`. Rewrite using `[← hcase]`.

Rewrite using `[hEq]`. Introduce and unpack `(⟨y, ⟨a, rfl⟩, rfl⟩ | ⟨y, ⟨b, rfl⟩, rfl⟩)`. Use `⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inl a))).down, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2]`. Use `congr 1`.

Rewrite using `[ULift.up_down, Equiv.symm_apply_apply]`. Use `⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inr b))).down, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h3]`. Use `congr 1`. Rewrite using `[ULift.up_down, Equiv.symm_apply_apply]`.

Rewrite using `[coordSubspaceIdeal_univ_eq_ofIdealTop, coordSubspaceIdeal_univ_eq_ofIdealTop, coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span, comap_ofIdealTop_span, comap_ofIdealTop_span, ← ofIdealTop_sup, ← Ideal.span_union, hset]`.
-/
private theorem coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv (k : Type u) [Field k] (c q : ℕ) :
    (coordSubspaceIdeal k (c + q) Finset.univ).comap
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
      = (coordSubspaceIdeal k c Finset.univ).comap (projLeft k c q)
        ⊔ (coordSubspaceIdeal k q Finset.univ).comap (projRight k c q) := by
  have h1 : ∀ i : ULift.{u, 0} (Fin (c + q)),
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i)
        = AffineSpace.coord (Spec (CommRingCat.of k)) ((uliftFinSumEquiv.{u} c q).symm i) := by
    intro i
    simp [affineSpaceIsoOfEquiv]
  have h2 : ∀ a : Fin c,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inl a) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro a
    simp
  have h3 : ∀ b : Fin q,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inr b) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro b
    simp
  have hset :
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom)) ''
        Set.range (fun i : Fin (c + q) =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i))
      = (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q))) ''
          Set.range (fun a : Fin c =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)))
        ∪ (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q))) ''
          Set.range (fun b : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      rw [h1]
      rcases hcase : ((uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)).down with a | b
      · refine Or.inl ⟨_, ⟨a, rfl⟩, ?_⟩
        rw [h2]
        have hEq : ULift.up.{u, 0} (Sum.inl a : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
      · refine Or.inr ⟨_, ⟨b, rfl⟩, ?_⟩
        rw [h3]
        have hEq : ULift.up.{u, 0} (Sum.inr b : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
    · rintro (⟨y, ⟨a, rfl⟩, rfl⟩ | ⟨y, ⟨b, rfl⟩, rfl⟩)
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inl a))).down, rfl⟩, ?_⟩
        rw [h1, h2]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inr b))).down, rfl⟩, ?_⟩
        rw [h1, h3]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
  rw [coordSubspaceIdeal_univ_eq_ofIdealTop, coordSubspaceIdeal_univ_eq_ofIdealTop,
    coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span, comap_ofIdealTop_span,
    comap_ofIdealTop_span, ← ofIdealTop_sup, ← Ideal.span_union, hset]

/- English proof (translation)
Establish `hDaff : IsAffine (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).toScheme)` using `(isAffineOpen_top (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))).basicOpen Δ`. Establish `hker' : Scheme.Hom.ker ρ' = (Scheme.Hom.ker ρ).comap (projLeft k M n) ⊔ Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))`. Rewrite using `[ker_eq_ofIdealTop_ker_appTop ρ', hker, ofIdealTop_sup, ker_eq_ofIdealTop_ker_appTop ρ, Scheme.IdealSheafData.comap_ofIdealTop]`. Establish `hcomapEq : (coordSubspaceIdeal k q Finset.univ).comap (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) ≫ projRight k M q) = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap ((affineSpaceIndexedBy k (ULi …`. Establish `hset : ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) ≫ projRight k M q))) '' Set.range (fun j : Fin q => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j)) = ⇑(Com …`.

Rewrite using `[← Set.range_comp, ← Set.range_comp]`. Use `congrArg Set.range (funext fun j => ?_)` and prove the remaining obligations. Use `show (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) ≫ projRight k M q))) (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j)) = (ConcreteCategory.hom (Scheme.Hom.app …`. Rewrite using `[appTop_comp_hom_apply, projRight_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inr]`. Rewrite using `[coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span, comap_ofIdealTop_span, hset]`.

Introduce `x`. Take `⟨U₀, hU₀, q₀, hq₀s, hq₀o, hq₀k⟩` from `hρ (g.base x)`. Use `hq₀s` as an intermediate fact. Establish `hmem1 : (projLeft k M n).base (ρ'.base x) ∈ U₀`. Establish `hb : (ρ' ≫ projLeft k M n).base x = (g ≫ ρ).base x` using `by rw [hcomm]`.

Simplify using `using (hb ▸ hU₀ : _)`. Establish `hmem2 : ρ'.base x ∈ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ`. Establish `hx : x ∈ ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)`. Rewrite using `[hD]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `hx`. Use `set U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens := (projLeft k M n ⁻¹ᵁ U₀) ⊓ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) with hUdef`. Establish `hUD : U ≤ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ`. Rewrite using `[hUdef]`. Conclude with `inf_le_right`.

Use `set G : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) := (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).homOfLE hUD ≫ graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) with hGdef`. Establish `hGproj : G ≫ projLeft k M q = U.ι ≫ projLeft k M n`. Rewrite using `[hGdef, Category.assoc, graphMorphismToAffineSpace_comp_projLeft, ← Category.assoc, Scheme.homOfLE_ι]`. Establish `hsub : Set.range ⇑G.base ⊆ Set.range ⇑(projLeft k M q ⁻¹ᵁ U₀).ι.base`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `y ⟨z, rfl⟩`. Establish `hz : (G ≫ projLeft k M q).base z = (U.ι ≫ projLeft k M n).base z` using `by rw [hGproj]`. Establish `hz' : (projLeft k M q).base (G.base z) = (projLeft k M n).base (U.ι.base z)`. Simplify using `using hz`. Use `show (projLeft k M q).base (G.base z) ∈ U₀`.

Rewrite using `[hz']`. Establish `hzU : U.ι.base z ∈ U` using `z.2`. Conclude with `hzU.1`. Use `set L : U.toScheme ⟶ (projLeft k M q ⁻¹ᵁ U₀).toScheme := IsOpenImmersion.lift (projLeft k M q ⁻¹ᵁ U₀).ι G hsub with hLdef`. Establish `hLfac : L ≫ (projLeft k M q ⁻¹ᵁ U₀).ι = G` using `IsOpenImmersion.lift_fac _ _ hsub`.

Establish `hGsmooth : Smooth G`. Rewrite using `[hGdef]`. Use `hsmooth` as an intermediate fact. Use `infer_instance`. Establish `hLsmooth : Smooth L`.

Use `smooth_of_smooth_comp_isOpenImmersion L (projLeft k M q ⁻¹ᵁ U₀).ι ?_` and prove the remaining obligations. Rewrite using `[hLfac]`. Conclude with `hGsmooth`. Use `set P : (projLeft k M q ⁻¹ᵁ U₀).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c ⊕ Fin q)) := prodMapOnPreimage k M q c U₀ q₀ with hPdef`. Establish `hPsmooth : Smooth P` using `smooth_prodMapOnPreimage hsm k M q c U₀ q₀ hq₀o`.

Use `set chart : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (c + q))) := L ≫ P ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom with hchartdef`. Use `⟨U, ⟨hmem1, hmem2⟩, chart, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hLsmooth` as an intermediate fact. Use `hPsmooth` as an intermediate fact. Rewrite using `[hchartdef]`.

Use `infer_instance`. Rewrite using `[hchartdef, Category.assoc, Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec, hPdef, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec, ← Category.assoc, hLfac, hGdef, Category.assoc, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec, ← Category.assoc, Scheme.homOfL …`. Establish `hA : (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q) = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n)`. Rewrite using `[hPdef, ← morphismRestrict_projLeft_comp k M q c U₀ q₀ hq₀o, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hq₀k, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, morphismRestrict_ι, ← Categor …`. Establish `hB : (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q) = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι`.

Rewrite using `[hPdef, prodMapOnPreimage_comp_projRight, ← Category.assoc, hLfac, hGdef, Category.assoc, Scheme.IdealSheafData.comap_comp, hcomapEq, ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`. Establish `key : (coordSubspaceIdeal k (c + q) Finset.univ).comap chart = (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q) ⊔ (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q)`. Rewrite using `[hchartdef, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_sup]`. Simplify using `only [← Scheme.IdealSheafData.comap_comp]`. Establish `key2 : restrictIdeal (Scheme.Hom.ker ρ') U = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n) ⊔ (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι`.

Rewrite using `[restrictIdeal_eq_comap_ι, hker', Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp]`. Rewrite using `[key2, key, hA, hB]`.
-/
theorem hasSmoothCoordCodim_add_of_smooth_graphMorphism (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (M c n q : ℕ)
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (hρ : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c)
    (g : A' ⟶ A)
    (ρ' : A' ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))) [IsClosedImmersion ρ']
    (hcomm : ρ' ≫ projLeft k M n = g ≫ ρ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (Δ : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ')) =
      Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k M n)))
          (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ))) ⊔
        Ideal.span (Set.range F))
    (hD : ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) = ⊤)
    (hsmooth : Smooth (graphMorphismToAffineSpace k M n q F
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))) ρ' (c + q) := by
  classical
  have hDaff : IsAffine
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).toScheme) :=
    (isAffineOpen_top (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))).basicOpen Δ
  have hker' : Scheme.Hom.ker ρ' =
      (Scheme.Hom.ker ρ).comap (projLeft k M n) ⊔
        Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F)) := by
    rw [ker_eq_ofIdealTop_ker_appTop ρ', hker, ofIdealTop_sup,
      ker_eq_ofIdealTop_ker_appTop ρ, Scheme.IdealSheafData.comap_ofIdealTop]
  have hcomapEq : (coordSubspaceIdeal k q Finset.univ).comap
        (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
          ≫ projRight k M q)
      = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι := by
    have hset :
        ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q))) ''
          Set.range (fun j : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
        = ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) ''
          Set.range F := by
      rw [← Set.range_comp, ← Set.range_comp]
      refine congrArg Set.range (funext fun j => ?_)
      show (ConcreteCategory.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q)))
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
          = (ConcreteCategory.hom (Scheme.Hom.appTop
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) (F j)
      rw [appTop_comp_hom_apply, projRight_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inr]
    rw [coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span,
      comap_ofIdealTop_span, hset]
  intro x
  obtain ⟨U₀, hU₀, q₀, hq₀s, hq₀o, hq₀k⟩ := hρ (g.base x)
  have := hq₀s
  have hmem1 : (projLeft k M n).base (ρ'.base x) ∈ U₀ := by
    have hb : (ρ' ≫ projLeft k M n).base x = (g ≫ ρ).base x := by rw [hcomm]
    simpa using (hb ▸ hU₀ : _)
  have hmem2 : ρ'.base x ∈
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    have hx : x ∈ ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) := by
      rw [hD]; trivial
    exact hx
  set U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens :=
    (projLeft k M n ⁻¹ᵁ U₀) ⊓
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) with hUdef
  have hUD : U ≤ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    rw [hUdef]; exact inf_le_right
  set G : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) :=
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).homOfLE hUD ≫
      graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
    with hGdef
  have hGproj : G ≫ projLeft k M q = U.ι ≫ projLeft k M n := by
    rw [hGdef, Category.assoc, graphMorphismToAffineSpace_comp_projLeft, ← Category.assoc, Scheme.homOfLE_ι]
  have hsub : Set.range ⇑G.base ⊆ Set.range ⇑(projLeft k M q ⁻¹ᵁ U₀).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : (G ≫ projLeft k M q).base z = (U.ι ≫ projLeft k M n).base z := by rw [hGproj]
    have hz' : (projLeft k M q).base (G.base z) = (projLeft k M n).base (U.ι.base z) := by
      simpa using hz
    show (projLeft k M q).base (G.base z) ∈ U₀
    rw [hz']
    have hzU : U.ι.base z ∈ U := z.2
    exact hzU.1
  set L : U.toScheme ⟶ (projLeft k M q ⁻¹ᵁ U₀).toScheme :=
    IsOpenImmersion.lift (projLeft k M q ⁻¹ᵁ U₀).ι G hsub with hLdef
  have hLfac : L ≫ (projLeft k M q ⁻¹ᵁ U₀).ι = G :=
    IsOpenImmersion.lift_fac _ _ hsub
  have hGsmooth : Smooth G := by
    rw [hGdef]
    have := hsmooth
    infer_instance
  have hLsmooth : Smooth L := by
    refine smooth_of_smooth_comp_isOpenImmersion L (projLeft k M q ⁻¹ᵁ U₀).ι ?_
    rw [hLfac]; exact hGsmooth
  set P : (projLeft k M q ⁻¹ᵁ U₀).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c ⊕ Fin q)) :=
    prodMapOnPreimage k M q c U₀ q₀ with hPdef
  have hPsmooth : Smooth P := smooth_prodMapOnPreimage hsm k M q c U₀ q₀ hq₀o
  set chart : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (c + q))) :=
    L ≫ P ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
    with hchartdef
  refine ⟨U, ⟨hmem1, hmem2⟩, chart, ?_, ?_, ?_⟩
  · have := hLsmooth
    have := hPsmooth
    rw [hchartdef]
    infer_instance
  · rw [hchartdef, Category.assoc, Category.assoc,
      affineSpaceIsoOfEquiv_hom_comp_toSpec, hPdef, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
      hLfac, hGdef, Category.assoc, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec, ← Category.assoc, Scheme.homOfLE_ι]
  · have hA : (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n) := by
      rw [hPdef, ← morphismRestrict_projLeft_comp k M q c U₀ q₀ hq₀o,
        Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hq₀k,
        restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hLfac, hGproj]
    have hB : (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q)
        = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [hPdef, prodMapOnPreimage_comp_projRight, ← Category.assoc, hLfac, hGdef, Category.assoc,
        Scheme.IdealSheafData.comap_comp, hcomapEq, ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have key : (coordSubspaceIdeal k (c + q) Finset.univ).comap chart
        = (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
          ⊔ (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q) := by
      rw [hchartdef, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
        coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv, Scheme.IdealSheafData.comap_sup,
        Scheme.IdealSheafData.comap_sup]
      simp only [← Scheme.IdealSheafData.comap_comp]
    have key2 : restrictIdeal (Scheme.Hom.ker ρ') U
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n)
          ⊔ (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [restrictIdeal_eq_comap_ι, hker', Scheme.IdealSheafData.comap_sup,
        ← Scheme.IdealSheafData.comap_comp]
    rw [key2, key, hA, hB]

/- English proof (translation)
Introduce `k _ _ X Y A pX pY pA _ _ _ _ i _ hi M c ρ _ hρ hρc r h _ hh y`. Take `⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb, n, q, hnqr, σ, hσci, hσcomm, F, Δ, hkerσ, hDtop, hgrsm⟩` from `hgr k X Y A pX pY pA i hi M ρ hρ r h hh y`. Use `hA'aff` as an intermediate fact. Use `hσci` as an intermediate fact. Use `⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb, n, by omega, ?_⟩` and prove the remaining obligations.

Introduce `N hN`. Take `⟨p, rfl⟩ : ∃ p, N = n + p` from `⟨N - n, by omega⟩`. Rewrite using `[show M + (n + p) = M + n + p from by omega, show c + (n + p - r) = c + q + p from by omega]`. Establish `hcc : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))) σ (c + q)` using `hasSmoothCoordCodim_add_of_smooth_graphMorphism hsm k M c n q ρ hρc g σ hσcomm F Δ hkerσ hDtop hgrsm`. Establish `hcc1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n)))) (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) (c + q)` using `HasSmoothCoordCodim.comp_iso_hom hcc (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))) (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n)))) (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M n))`.

Establish `: IsClosedImmersion (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom)` using `inferInstance`. Establish `hpad` using `HasSmoothCoordCodim.comp_affineSpaceInl_affineSpaceIsoOfEquiv hsm k (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) p hcc1`. Use `⟨(σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) ≫ affineSpaceInl k (M + n) p ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom, inferInstance, ?_, hpad⟩` and prove the remaining obligations. Establish `hstruct : affineSpaceInl k (M + n) p ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n + p))) = affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n)))`. Rewrite using `[affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec]`.

Simplify using `only [Category.assoc]`. Rewrite using `[hstruct, affineSpaceIsoOfEquiv_hom_comp_toSpec, ← projLeft_comp_affineSpaceIndexedByToSpec, ← Category.assoc, hσcomm, Category.assoc, hρ, hgpA]`.
-/
theorem smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart (hsm : AffineSpaceIsSmooth.{u})
    (hgr : SmoothPullbackHasGraphChart.{u}) : SmoothPullbackHasLocalAmbientEmbedding.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ hi M c ρ _ hρ hρc r h _ hh y
  obtain ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci,
    hjpb, n, q, hnqr, σ, hσci, hσcomm, F, Δ, hkerσ, hDtop, hgrsm⟩ :=
      hgr k X Y A pX pY pA i hi M ρ hρ r h hh y
  have := hA'aff
  have := hσci
  refine ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb,
    n, by omega, ?_⟩
  intro N hN
  obtain ⟨p, rfl⟩ : ∃ p, N = n + p := ⟨N - n, by omega⟩
  rw [show M + (n + p) = M + n + p from by omega,
    show c + (n + p - r) = c + q + p from by omega]
  have hcc : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      σ (c + q) :=
    hasSmoothCoordCodim_add_of_smooth_graphMorphism hsm k M c n q ρ hρc g σ hσcomm F Δ hkerσ hDtop hgrsm
  have hcc1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom)
      (c + q) :=
    HasSmoothCoordCodim.comp_iso_hom hcc
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M n))
  have : IsClosedImmersion
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  have hpad := HasSmoothCoordCodim.comp_affineSpaceInl_affineSpaceIsoOfEquiv hsm k
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) p hcc1
  refine ⟨(σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) ≫
      affineSpaceInl k (M + n) p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom,
    inferInstance, ?_, hpad⟩
  have hstruct : affineSpaceInl k (M + n) p ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n + p)))
      = affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))) := by
    rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec]
  simp only [Category.assoc]
  rw [hstruct, affineSpaceIsoOfEquiv_hom_comp_toSpec, ← projLeft_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
    hσcomm, Category.assoc, hρ, hgpA]

end FunctorialResolution.EmbeddedResolution

end
