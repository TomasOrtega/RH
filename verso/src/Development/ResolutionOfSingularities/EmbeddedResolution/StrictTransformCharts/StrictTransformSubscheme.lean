import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Given an element of the source of the isomorphism, take its image under the forward map. The inverse sends this image back to the original element, so it is surjective.
-/
private theorem surjective_hom_iso_inv {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨CommRingCat.Hom.hom e.hom a, ?_⟩
  simp

/- English proof (authored)
On the affine open, the section map of the subscheme inclusion is the quotient map by its ideal followed by the isomorphism with sections on the inverse-image open. The quotient map and the isomorphism are both surjective.
-/
private theorem surjective_subschemeι_app {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) :
    Function.Surjective (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) := by
  rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.coe_comp]
  exact (surjective_hom_iso_inv (I.subschemeObjIso U)).comp Ideal.Quotient.mk_surjective

/- English proof (authored)
The inverse images of affine opens of the ambient scheme are affine and cover the closed subscheme. Their section rings are quotients of the ambient affine section rings, which are Noetherian. Quotients of Noetherian rings are Noetherian, so this affine cover proves that the subscheme is locally Noetherian.
-/
theorem isLocallyNoetherian_subscheme {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) : IsLocallyNoetherian I.subscheme := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun U : Y.affineOpens =>
      (⟨I.subschemeι ⁻¹ᵁ (U : Y.Opens), isAffineOpen_preimage_subschemeι I U.2⟩ :
        I.subscheme.affineOpens)) ?_ ?_
  · ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : I.subschemeι.base x ∈ (⨆ V : Y.affineOpens, (V : Y.Opens)) := by
      rw [iSup_affineOpens_eq_top Y]
      trivial
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨V, hV⟩
  · intro U
    have := IsLocallyNoetherian.component_noetherian U
    exact isNoetherianRing_of_surjective _ _ _ (surjective_subschemeι_app I U)

/- English proof (authored)
The support of the restricted ideal is the inverse image of the original support. Since the restricted ideal is the unit ideal, its support is empty. Thus a point in the open cannot belong to the original support.
-/
theorem notMem_support_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (U : Y.Opens) (x : Y) (hx : x ∈ U) (h : restrictIdeal D U = ⊤) : x ∉ D.support :=
  Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top D h hx

/- English proof (authored)
Extend each of the equal image ideals along the second homomorphism. Successive extensions agree with extension along the composite, which is the identity. This recovers the original ideals on both sides, giving equality.
-/
private theorem ideal_eq_of_map_eq_of_comp_eq_id {R S : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ R)
    (hfg : f ≫ g = 𝟙 R) {I J : Ideal R}
    (hIJ : Ideal.map (CommRingCat.Hom.hom f) I = Ideal.map (CommRingCat.Hom.hom f) J) : I = J := by
  have key : ∀ K : Ideal R,
      Ideal.map (CommRingCat.Hom.hom g) (Ideal.map (CommRingCat.Hom.hom f) K) = K := by
    intro K
    rw [Ideal.map_map, ← CommRingCat.hom_comp, hfg, CommRingCat.hom_id, Ideal.map_id]
  rw [← key I, hIJ, key J]

/- English proof (authored)
Any endomorphism of an open in the opposite of the poset of opens is the identity. The presheaf sends it to the identity on sections.
-/
private theorem presheaf_map_eq_id {Y : Scheme.{u}} {P : (Y.Opens)ᵒᵖ} (f : P ⟶ P) :
    Y.presheaf.map f = 𝟙 (Y.presheaf.obj P) := by
  have hf : f = 𝟙 P := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hf, CategoryTheory.Functor.map_id]

/- English proof (authored)
Functoriality gives the map of the composite of the three arrows. This composite is an endomorphism of an open, hence the identity. Its map on sections is therefore the identity.
-/
private theorem presheaf_map_comp_comp_eq_id {Y : Scheme.{u}} {P Q R : (Y.Opens)ᵒᵖ}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ P) :
    (Y.presheaf.map f ≫ Y.presheaf.map g) ≫ Y.presheaf.map h = 𝟙 (Y.presheaf.obj P) := by
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  exact presheaf_map_eq_id _

/- English proof (authored)
The equal restrictions have equal ideals of global sections on the affine open subscheme. Those ideals are extensions of the original section ideals along the canonical isomorphism from ambient sections on the open. Extending back along the inverse isomorphism gives equality of the original ideals.
-/
theorem ideal_eq_of_restrictIdeal_eq {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (V : Y.affineOpens) (h : restrictIdeal A (V : Y.Opens) = restrictIdeal B (V : Y.Opens)) :
    A.ideal V = B.ideal V := by
  have : IsAffine (Scheme.Opens.toScheme (V : Y.Opens)) := V.2
  have e : (⊤ : (Scheme.Opens.toScheme (V : Y.Opens)).Opens) ≤
      Scheme.Opens.ι (V : Y.Opens) ⁻¹ᵁ (V : Y.Opens) := by
    intro x _
    exact x.2
  have h' : A.comap (Scheme.Opens.ι (V : Y.Opens)) = B.comap (Scheme.Opens.ι (V : Y.Opens)) := by
    simpa only [restrictIdeal_eq_comap_ι] using h
  have hA := AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE A
    (Scheme.Opens.ι (V : Y.Opens)) V ⟨⊤, isAffineOpen_top _⟩ e
  have hB := AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE B
    (Scheme.Opens.ι (V : Y.Opens)) V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h'] at hA
  refine (ideal_eq_of_map_eq_of_comp_eq_id
    (Scheme.Hom.appLE (Scheme.Opens.ι (V : Y.Opens)) (V : Y.Opens) ⊤ e)
    (Scheme.Opens.topIso (V : Y.Opens)).hom ?_ (hB.symm.trans hA)).symm
  simp [AlgebraicGeometry.Scheme.Hom.appLE]
  exact presheaf_map_comp_comp_eq_id _ _ _

private def colonSpanSingleton {R : Type*} [CommRing R] (J : Ideal R) (x : R) : Ideal R where
  carrier := {r | r * x ∈ J}
  add_mem' := fun {a b} ha hb => by
    show (a + b) * x ∈ J
    rw [add_mul]
    exact J.add_mem ha hb
  zero_mem' := by
    show (0 : R) * x ∈ J
    rw [zero_mul]
    exact J.zero_mem
  smul_mem' := fun c a ha => by
    show (c • a) * x ∈ J
    rw [smul_eq_mul, mul_assoc]
    exact J.mul_mem_left c ha

/- English proof (authored)
The ideal quotient by the chosen element is defined to consist of the multipliers whose product with that element belongs to the original ideal. This definition gives the stated equivalence.
-/
private theorem mem_colonSpanSingleton {R : Type*} [CommRing R] (J : Ideal R) (x r : R) :
    r ∈ colonSpanSingleton J x ↔ r * x ∈ J := Iff.rfl

/- English proof (authored)
Write the localized element as a fraction with numerator in the ideal and denominator a power of the inverted element. Cross-multiply and then multiply by a further power to make the resulting equality hold in the original ring. The product of the powers times the original element is in the ideal.
-/
private theorem exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (J : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) J) : ∃ n : ℕ, f ^ n * x ∈ J := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) S] at hx
  obtain ⟨⟨a, m⟩, hxa⟩ := hx
  rw [← map_mul] at hxa
  obtain ⟨c, hcx⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) S).mp hxa
  obtain ⟨q, hq⟩ := m.2
  obtain ⟨p, hp⟩ := c.2
  refine ⟨p + q, ?_⟩
  have key : f ^ (p + q) * x = (c : R) * (x * (m : R)) := by
    rw [← hp, ← hq]; ring
  rw [key, hcx]
  exact J.mul_mem_left _ a.2

/- English proof (authored)
Take a section of the first ideal on an affine open. For each point of that open choose a basic neighborhood inside a member of the given cover. The two section ideals agree on this basic open because their restrictions agree on the cover member. Clearing denominators shows that a positive power of the basic-open section sends the original section into the second ideal. The basic opens of those powers still cover the affine open, so the powers generate the unit ideal. A linear combination giving one shows that the original section belongs to the second ideal there.
-/
private theorem ideal_le_of_restrictIdeal_eq_of_iSup_eq_top {Y : Scheme.{u}} {ι : Type*}
    (A B : Y.IdealSheafData) (U : ι → Y.Opens) (hU : (⨆ i, U i) = ⊤)
    (h : ∀ i, restrictIdeal A (U i) = restrictIdeal B (U i))
    (V : Y.affineOpens) : A.ideal V ≤ B.ideal V := by
  intro x hx
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  obtain ⟨T, hT⟩ :
      ∃ T : Ideal ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens))),
        ∀ r, r ∈ T ↔ r * x ∈ B.ideal V :=
    ⟨colonSpanSingleton (B.ideal V) x, mem_colonSpanSingleton (B.ideal V) x⟩
  have hcover : (V : Y.Opens) ≤
      ⨆ g : (T : Set ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))),
        Y.basicOpen (g : ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) := by
    intro y hy
    have hy' : y ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (⟨y, hyi⟩ : ↥(U i)) hy
    have hAB : A.ideal (Y.affineBasicOpen f) = B.ideal (Y.affineBasicOpen f) :=
      ideal_eq_of_restrictIdeal_eq A B (Y.affineBasicOpen f)
        (restrictIdeal_eq_of_le_of_eq hfle (h i))
    have := hV.isLocalization_basicOpen f
    have halg : algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f))) =
        (Y.presheaf.map (CategoryTheory.homOfLE (Y.basicOpen_le f)).op).hom := rfl
    have hmem : algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f))) x ∈
        Ideal.map (algebraMap ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
          ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen f)))) (B.ideal V) := by
      rw [halg, B.map_ideal_basicOpen V f, ← hAB, ← A.map_ideal_basicOpen V f]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway f (B.ideal V) x hmem
    have hgT : f ^ (n + 1) ∈ T := by
      have hmul : f ^ (n + 1) * x ∈ B.ideal V := by
        have hfx : f ^ (n + 1) * x = f * (f ^ n * x) := by ring
        rw [hfx]
        exact Ideal.mul_mem_left _ _ hn
      exact (hT _).mpr hmul
    have hyg : y ∈ Y.basicOpen (f ^ (n + 1)) := by
      rw [AlgebraicGeometry.Scheme.basicOpen_pow]
      · exact hyf
      · exact Nat.succ_pos n
    exact Opens.mem_iSup.mpr ⟨⟨f ^ (n + 1), hgT⟩, hyg⟩
  have hspan : Ideal.span (T : Set ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) = ⊤ :=
    hV.self_le_iSup_basicOpen_iff.mp hcover
  have hTtop : T = ⊤ := by
    rw [← Ideal.span_eq T, hspan]
  have h1 : (1 : ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))) ∈ T := by
    rw [hTtop]; exact Submodule.mem_top
  have h2 := (hT 1).mp h1
  rwa [one_mul] at h2

/- English proof (authored)
Equality on the cover implies on each affine open that the first section ideal is contained in the second, by the basic-open argument. Reversing the equality on the cover gives the opposite containment. The affine section ideals determine the sheaves.
-/
theorem eq_of_restrictIdeal_eq_of_iSup_eq_top {Y : Scheme.{u}} {ι : Type*}
    (A B : Y.IdealSheafData) (U : ι → Y.Opens) (hU : (⨆ i, U i) = ⊤)
    (h : ∀ i, restrictIdeal A (U i) = restrictIdeal B (U i)) : A = B :=
  AlgebraicGeometry.Scheme.IdealSheafData.ext
    (funext fun V =>
      le_antisymm (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top A B U hU h V)
        (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top B A U hU (fun i => (h i).symm) V))

/- English proof (authored)
Choose one neighborhood with equal restrictions for each point. These neighborhoods cover the whole scheme, so the equality criterion on an open cover gives equality of the ideal sheaves.
-/
theorem eq_of_locally_restrictIdeal_eq {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (h : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ restrictIdeal A U = restrictIdeal B U) : A = B := by
  choose U hxU hAB using h
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top A B U ?_ hAB
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/- English proof (authored)
The section of the ambient ideal maps to zero under the quotient describing sections on the inverse image of the affine open. The map to the smaller open further restricts that zero section, so it also sends the original section to zero.
-/
private theorem appLE_subschemeι_apply_eq_zero_of_mem {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) (V : I.subscheme.Opens)
    (e : V ≤ (Opens.map I.subschemeι.base).obj (U : Y.Opens))
    {t : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))} (ht : t ∈ I.ideal U) :
    (CommRingCat.Hom.hom (I.subschemeι.appLE (U : Y.Opens) V e)) t = 0 := by
  have happ : (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) t = 0 := by
    rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero]
  have hcomp : I.subschemeι.appLE (U : Y.Opens) V e =
      I.subschemeι.app (U : Y.Opens) ≫ I.subscheme.presheaf.map (homOfLE e).op := rfl
  rw [hcomp, CommRingCat.hom_comp, RingHom.comp_apply, happ, map_zero]

/- English proof (authored)
The section ring of the inverse image is isomorphic to the quotient by the given section ideal. If one equals zero in that ring, then the quotient class of one is zero. Thus one belongs to the original ideal and the ideal is the unit ideal.
-/
private theorem ideal_eq_top_of_one_eq_zero {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens)
    (h1 : (1 : ↑(I.subscheme.presheaf.obj
      (Opposite.op ((Opens.map I.subschemeι.base).obj (U : Y.Opens))))) = 0) :
    I.ideal U = ⊤ := by
  have happ : (CommRingCat.Hom.hom (I.subschemeι.app (U : Y.Opens))) 1 = 0 := by
    rw [map_one]
    exact h1
  rw [Scheme.IdealSheafData.subschemeι_app, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at happ
  have h2 := congrArg (CommRingCat.Hom.hom (I.subschemeObjIso U).hom) happ
  have h4 : (CommRingCat.Hom.hom (I.subschemeObjIso U).hom) 0 = 0 := map_zero _
  have h5 := CommRingCat.hom_inv_apply (I.subschemeObjIso U)
      ((Ideal.Quotient.mk (I.ideal U)) (1 : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))))
  have h3 : (Ideal.Quotient.mk (I.ideal U))
      (1 : ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens)))) = 0 :=
    h5.symm.trans (h2.trans h4)
  exact (Ideal.eq_top_iff_one _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h3)

/- English proof (authored)
Suppose the hypersurface coordinate is outside the center index set. Its image in the quotient by the center is then a coordinate of the induced étale chart, so it is a nonzerodivisor. On the other hand, the hypersurface ideal is contained in the center ideal, so that coordinate maps to zero in the quotient. Since zero is a nonzerodivisor there, one equals zero. This makes the center ideal the unit ideal on the affine chart, contradicting the presence of the given center point. Therefore the hypersurface index lies in the center set.
-/
theorem mem_of_restrictIdeal_eq_coordIdeal_of_le {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (Z H : X.IdealSheafData) (S : Finset (Fin m)) (a : Fin m)
    (hHZ : H ≤ Z) (hH : restrictIdeal H U = c.coordIdeal {a})
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : X) (hxU : x ∈ U) (hxZ : x ∈ Z.support) : a ∈ S := by
  by_contra ha
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S ha
  have hHid := c.ideal_eq_span_coord hU H {a} hH
  have hmemH : c.coord a ∈ H.ideal ⟨U, hU⟩ := by
    rw [hHid]
    refine Ideal.subset_span ⟨a, ?_, rfl⟩
    simp
  have hmem : c.coord a ∈ Z.ideal ⟨U, hU⟩ := hHZ ⟨U, hU⟩ hmemH
  have hV : IsAffineOpen ((Opens.map Z.subschemeι.base).obj U) :=
    isAffineOpen_preimage_subschemeι Z hU
  have hcoord : (c.restrictToSubscheme hU Z S hZ).coord i = 0 := by
    rw [EtaleChart.restrictToSubscheme_coord, hi]
    exact appLE_subschemeι_apply_eq_zero_of_mem Z ⟨U, hU⟩ _ _ hmem
  have hnz := coord_mem_nonZeroDivisors hV (c.restrictToSubscheme hU Z S hZ) i
  have h1 := (mem_nonZeroDivisors_iff.mp hnz).1 1 (by rw [hcoord, zero_mul])
  have htop : Z.ideal ⟨U, hU⟩ = ⊤ := ideal_eq_top_of_one_eq_zero Z ⟨U, hU⟩ h1
  exact notMem_support_of_restrictIdeal_eq_top Z U x hxU
    ((Scheme.IdealSheafData.comap_ι_eq_top_iff_ideal_eq_top Z hU).mpr htop) hxZ

/- English proof (authored)
Identify the ideal with the kernel ideal of the closed immersion. The composite from the strict transform to the original scheme kills that kernel ideal and hence factors through the closed immersion. This gives the required map.
-/
private theorem exists_strictTransform_lift_of_ker_eq {X X₁ S : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (j : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion j] (H : X.IdealSheafData)
    (hker : j.ker = H) :
    ∃ q : (Blowup.strictTransform π Z H).subscheme ⟶ S,
      q ≫ j = (Blowup.strictTransform π Z H).subschemeι ≫ π := by
  subst hker
  exact exists_comp_eq_strictTransform_subschemeι_comp j π Z

/- English proof (authored)
The kernel ideal of the closed subscheme inclusion is the ideal defining it. Apply the lift for a closed immersion with that kernel to obtain a map from the strict transform into the original closed subscheme.
-/
theorem exists_strictTransformSubschemeLift {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    ∃ q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme,
      q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π :=
  exists_strictTransform_lift_of_ker_eq π Z H.subschemeι H
    (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι H)

def strictTransformSubschemeLift {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme :=
  (exists_strictTransformSubschemeLift π Z H).choose

/- English proof (authored)
The chosen lift is the factorization of the composite from the strict transform to the ambient scheme through the closed subscheme inclusion. Composing the lift with that inclusion gives the original composite by construction.
-/
theorem strictTransformSubschemeLift_comp_subschemeι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z H : X.IdealSheafData) :
    strictTransformSubschemeLift π Z H ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π :=
  (exists_strictTransformSubschemeLift π Z H).choose_spec

/- English proof (authored)
Identify the ideal with the kernel of the closed immersion. The given map and the canonical strict-transform lift have the same composite with that immersion. Since the immersion is a monomorphism, the maps agree. The canonical lift has the blowup property for the restricted center, so the given map does too.
-/
private theorem isBlowupAlongIdealSheaf_comap_of_ker_eq {X X₁ S : Scheme.{u}} [IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (j : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] (H : X.IdealSheafData) (hker : j.ker = H)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (q : (Blowup.strictTransform π Z H).subscheme ⟶ S)
    (hq : q ≫ j = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    Blowup.IsBlowupAlongIdealSheaf q (Z.comap j) := by
  subst hker
  have h2 : q ≫ j = strictTransformLiftOfClosedImmersion j π Z ≫ j := by
    rw [hq, strictTransformLiftOfClosedImmersion_comp]
  have hqq : q = strictTransformLiftOfClosedImmersion j π Z := (cancel_mono j).mp h2
  rw [hqq]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ

/- English proof (authored)
The original closed subscheme inclusion has the required kernel ideal, and the chosen lift factors the strict-transform inclusion followed by the ambient blowup. Apply the blowup property for such a lift along a closed immersion.
-/
theorem isBlowupAlongIdealSheaf_strictTransformSubschemeLift {X X₁ : Scheme.{u}} [IsLocallyNoetherian X₁]
    (π : X₁ ⟶ X) (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Blowup.IsBlowupAlongIdealSheaf (strictTransformSubschemeLift π Z H) (Z.comap H.subschemeι) :=
  isBlowupAlongIdealSheaf_comap_of_ker_eq π Z H.subschemeι H
    (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι H) hπ
    (strictTransformSubschemeLift π Z H) (strictTransformSubschemeLift_comp_subschemeι π Z H)

/- English proof (authored)
The range of the closed subscheme inclusion on points is the support of its ideal. The image of the given point belongs to that range.
-/
private theorem subschemeι_base_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (x : I.subscheme) : I.subschemeι.base x ∈ (I.support : Set X) := by
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  exact Set.mem_range_self x

/- English proof (authored)
Each coordinate ideal is obtained by pulling back the same coordinate-subspace ideal on affine space. The chart maps agree, so the two pulled-back ideals agree.
-/
private theorem coordIdeal_eq_of_map_eq {X : Scheme.{u}} {k : Type u} [Field k]
    {p₁ p₂ : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c₁ : EtaleChart p₁ U m) (c₂ : EtaleChart p₂ U m) (h : c₁.map = c₂.map) (T : Finset (Fin m)) :
    c₁.coordIdeal T = c₂.coordIdeal T := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  exact congrArg (fun f => (coordSubspaceIdeal k m T).comap f) h

/- English proof (authored)
Use the normal crossings chart at the center point and shrink its domain to an affine open. The selected hypersurface is the first list entry, and the indicated boundary member occurs in the tail. The chart assigns each either no coordinate, giving the unit ideal, or one coordinate. If both have coordinates, those indices differ because the two positions in the list are distinct and the assignment is injective on present entries. Shrinking preserves these descriptions and the center coordinate ideal.
-/
private theorem exists_etaleChart_of_hasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (D : X.IdealSheafData) (hD : D ∈ E) (y : X)
    (hy : y ∈ Z.support) :
    ∃ (U : X.Opens) (_ : y ∈ U) (_ : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m)
      (S : Finset (Fin m)) (_ : restrictIdeal Z U = c.coordIdeal S),
      restrictIdeal H U = ⊤ ∨ ∃ a : Fin m, restrictIdeal H U = c.coordIdeal {a} ∧
        (restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b}) := by
  obtain ⟨U, hyU, m, c, av, S, hinj, hnone, hsome, hZ⟩ := hsnc y hy
  obtain ⟨i, hi, hEi⟩ : ∃ (i : ℕ) (h : i < E.length), E[i] = D := List.mem_iff_getElem.mp hD
  have hlt0 : 0 < (H :: E).length := by rw [List.length_cons]; omega
  have hlti : i + 1 < (H :: E).length := by rw [List.length_cons]; omega
  have hH0 : ∀ t : Fin m, av 0 = some t → restrictIdeal H U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome 0 hlt0 t ht
    rw [List.getElem_cons_zero] at h
    exact h
  have hHn : av 0 = none → restrictIdeal H U = ⊤ := by
    intro ht
    have h := hnone 0 hlt0 ht
    rw [List.getElem_cons_zero] at h
    exact h
  have hD0 : ∀ t : Fin m, av (i + 1) = some t → restrictIdeal D U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome (i + 1) hlti t ht
    simp only [List.getElem_cons_succ] at h
    rw [hEi] at h
    exact h
  have hDn : av (i + 1) = none → restrictIdeal D U = ⊤ := by
    intro ht
    have h := hnone (i + 1) hlti ht
    simp only [List.getElem_cons_succ] at h
    rw [hEi] at h
    exact h
  obtain ⟨V, hVaff, hyV, hVle⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hyU
  refine ⟨V, hyV, hVaff, m, c.restrict hVle, S,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVle c Z S hZ, ?_⟩
  cases h0 : av 0 with
  | none => exact Or.inl (restrictIdeal_eq_top_of_le H hVle (hHn h0))
  | some t =>
      refine Or.inr ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c H {t} (hH0 t h0), ?_⟩
      cases h1 : av (i + 1) with
      | none => exact Or.inl (restrictIdeal_eq_top_of_le D hVle (hDn h1))
      | some t' =>
          refine Or.inr ⟨t', ?_, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c D {t'} (hD0 t' h1)⟩
          intro htt
          subst htt
          have hz := hinj 0 hlt0 (i + 1) hlti t' h0 h1
          omega

/- English proof (authored)
Choose a blowup chart above the downstairs open containing the image of the point. The hypersurface has unit ideal downstairs, so its strict transform has unit ideal on the chart. Its support is empty there. This contradicts the fact that the point maps into that support by the strict-transform inclusion.
-/
private theorem false_of_mem_preimage_of_restrictIdeal_eq_top {X X₁ : Scheme.{u}} {k : Type u}
    [Field k] {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X)
    (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) {S : Finset (Fin m)}
    (hZ : restrictIdeal Z U = c.coordIdeal S) (hHtop : restrictIdeal H U = ⊤)
    (x : (Blowup.strictTransform π Z H).subscheme)
    (hxU : (Blowup.strictTransform π Z H).subschemeι.base x ∈ π ⁻¹ᵁ U) : False := by
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ
    ((Blowup.strictTransform π Z H).subschemeι.base x) hxU
  have htop : restrictIdeal (Blowup.strictTransform π Z H)
      (blowupChartOfIsBlowup π c S hπ hZ s hs).domain = ⊤ :=
    (blowupChartOfIsBlowup π c S hπ hZ s hs).restrictIdeal_strictTransform_of_eq_top Z H hHtop
  exact notMem_support_of_restrictIdeal_eq_top (Blowup.strictTransform π Z H)
    (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
    ((Blowup.strictTransform π Z H).subschemeι.base x) hmem htop
    (subschemeι_base_mem_support (Blowup.strictTransform π Z H) x)

/- English proof (authored)
Take the open of the strict transform lying over the complement of the center. On this open the ambient strict transform of the other divisor agrees with its total transform. The point also lies off the restricted center for the map to the hypersurface, since the two pullbacks of the center agree by the factorization. The strict transform along the hypersurface map therefore agrees locally with its total transform as well. The two total transforms are pullbacks along equal composites, giving the desired equality on this open.
-/
private theorem exists_restrictIdeal_eq_of_notMem_support {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    [IsLocallyNoetherian X₁] (Z H : X.IdealSheafData)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) (x : (Blowup.strictTransform π Z H).subscheme)
    (hx : π.base ((Blowup.strictTransform π Z H).subschemeι.base x) ∉ Z.support) :
    ∃ W : (Blowup.strictTransform π Z H).subscheme.Opens, x ∈ W ∧
      restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι) W =
        restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι)) W := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian q
    (Z.comap H.subschemeι) (D.comap H.subschemeι)
  have hZcomap : (Z.comap H.subschemeι).comap q
      = (Z.comap π).comap (Blowup.strictTransform π Z H).subschemeι := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hq]
  have hVmem : ∀ z : X₁, z ∈ (π ⁻¹ᵁ Z.support.compl) → π.base z ∉ Z.support := fun z hz => hz
  have hWmem : ∀ z : (Blowup.strictTransform π Z H).subscheme,
      z ∈ ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) →
        q.base z ∉ (Z.comap H.subschemeι).support := by
    intro z hz hmem
    have h1 : z ∈ ((Z.comap H.subschemeι).comap q).support := by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
      exact hmem
    rw [hZcomap, AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h1
    have h2 : (Blowup.strictTransform π Z H).subschemeι.base z ∈ (Z.comap π).support := h1
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h2
    have h3 : π.base ((Blowup.strictTransform π Z H).subschemeι.base z) ∈ Z.support := h2
    have hz' : π.base ((Blowup.strictTransform π Z H).subschemeι.base z) ∉ Z.support := hz
    exact hz' h3
  refine ⟨(Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl), hx, ?_⟩
  rw [restrictIdeal_comap_eq_comap_resLE_restrictIdeal (Blowup.strictTransform π Z H).subschemeι
      (Blowup.strictTransform π Z D) (π ⁻¹ᵁ Z.support.compl)
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support π Z D _ hVmem,
    ← restrictIdeal_comap_eq_comap_resLE_restrictIdeal (Blowup.strictTransform π Z H).subschemeι
      (D.comap π) (π ⁻¹ᵁ Z.support.compl)
      ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support q (Z.comap H.subschemeι)
      (D.comap H.subschemeι) _ hWmem,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hq]

/- English proof (authored)
The hypersurface is a center coordinate distinct from the exceptional index. Restricting the chart to its strict transform removes that coordinate and identifies the smaller center with the remaining center coordinates. The distinguished index remains and determines the restricted blowup chart. If the other divisor has unit ideal downstairs, both restrictions are unit ideals. Otherwise it is a distinct coordinate, so it has a corresponding retained index on the hypersurface. If this index corresponds to the exceptional one, both strict transforms are empty on the chart. Otherwise both ideals are generated by the retained chart coordinate for that divisor. The chart induced by restriction and the chart for the hypersurface blowup use the same map, so their coordinate ideals agree.
-/
private theorem restrictIdeal_comap_strictTransform_eq_of_blowupChart {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} [IsLocallyNoetherian X₁]
    {U : X.Opens} {m : ℕ} {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}
    (B : BlowupChart π c S s) (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain)
    (Z H : X.IdealSheafData) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (D : X.IdealSheafData)
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π) :
    restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) =
      restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z H
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian q
    (Z.comap H.subschemeι) (D.comap H.subschemeι)
  have hsa : s ∉ ({a} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]
    exact fun h => has h.symm
  obtain ⟨s', hs'⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hsa
  have hs'S : s' ∈ complEmbPreimage m S a := mem_complEmbPreimage_of_complOrderEmb_eq m S a hs hs'
  have hZ' : restrictIdeal (Z.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)
      = (c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a) :=
    restrictIdeal_comap_subschemeι_eq_coordIdeal c hU Z H S a hZ hH
  have hFa : restrictIdeal (Blowup.strictTransform π Z H) B.domain = B.chart.coordIdeal {a} :=
    B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH
  have hBmap : (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart.map
      = (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa).map :=
    B.restrictToStrictTransform_chart_map hU hB Z H hs hZ a ha has hH s' hs' q hq
  rcases hDd with hDtop | ⟨b, hba, hDb⟩
  · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ :=
      restrictIdeal_comap_subschemeι_eq_top (Blowup.strictTransform π Z H) B.domain
        (Blowup.strictTransform π Z D) (B.restrictIdeal_strictTransform_of_eq_top Z D hDtop)
    have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
        ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
      have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
          hs' q hq).restrictIdeal_strictTransform_of_eq_top (Z.comap H.subschemeι)
          (D.comap H.subschemeι) (restrictIdeal_comap_subschemeι_eq_top H U D hDtop)
      exact h
    rw [hL, hR]
  · have hb : b ∉ ({a} : Finset (Fin m)) := by
      simp only [Finset.mem_singleton]
      exact hba
    obtain ⟨b', hb'⟩ := exists_complOrderEmb_eq m ({a} : Finset (Fin m)) hb
    have hDb' : restrictIdeal D U = c.coordIdeal {complOrderEmb m {a} b'} := by
      rw [hb']
      exact hDb
    have hRD : restrictIdeal (D.comap H.subschemeι) (H.subschemeι ⁻¹ᵁ U)
        = (c.restrictToSubscheme hU H {a} hH).coordIdeal {b'} :=
      EtaleChart.restrictToSubscheme_coordIdeal_singleton c hU H {a} hH b' D hDb'
    have hiff : (b = s) ↔ (b' = s') := by
      constructor
      · intro h
        apply (complOrderEmb m ({a} : Finset (Fin m))).injective
        rw [hb', hs', h]
      · intro h
        rw [← hb', ← hs', h]
    by_cases hbs : b = s
    · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
        refine restrictIdeal_comap_subschemeι_eq_top (Blowup.strictTransform π Z H) B.domain
          (Blowup.strictTransform π Z D) ?_
        rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_pos hbs]
      have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain) = ⊤ := by
        have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
            hs' q hq).restrictIdeal_strictTransform_coordIdeal (Z.comap H.subschemeι)
            (D.comap H.subschemeι) hs'S hZ' b' hRD
        rw [if_pos (hiff.mp hbs)] at h
        exact h
      rw [hL, hR]
    · have hL : restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι)
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          = (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa).coordIdeal {b'} := by
        refine EtaleChart.restrictToSubscheme_coordIdeal_singleton B.chart hB
          (Blowup.strictTransform π Z H) {a} hFa b' (Blowup.strictTransform π Z D) ?_
        rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_neg hbs, hb']
      have hR : restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι))
          ((Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ B.domain)
          = (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
              hs' q hq).chart.coordIdeal {b'} := by
        have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
            hs' q hq).restrictIdeal_strictTransform_coordIdeal (Z.comap H.subschemeι)
            (D.comap H.subschemeι) hs'S hZ' b' hRD
        rw [if_neg (fun hxx => hbs (hiff.mpr hxx))] at h
        exact h
      rw [hL, hR]
      exact coordIdeal_eq_of_map_eq
        (B.chart.restrictToSubscheme hB (Blowup.strictTransform π Z H) {a} hFa)
        (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart
        hBmap.symm {b'}

/- English proof (authored)
Choose a blowup chart containing the image of the point. The hypersurface index differs from the distinguished index, because if they agreed its strict transform would be empty on this chart. Shrink the chart to an affine neighborhood of the image and pull that open back to the strict transform. The affine chart comparison gives the required equality on that neighborhood.
-/
private theorem exists_restrictIdeal_eq_of_mem_preimage {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m)
    {S : Finset (Fin m)} (hZ : restrictIdeal Z U = c.coordIdeal S) {a : Fin m} (ha : a ∈ S)
    (hH : restrictIdeal H U = c.coordIdeal {a})
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (x : (Blowup.strictTransform π Z H).subscheme)
    (hxU : (Blowup.strictTransform π Z H).subschemeι.base x ∈ π ⁻¹ᵁ U) :
    ∃ W : (Blowup.strictTransform π Z H).subscheme.Opens, x ∈ W ∧
      restrictIdeal ((Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι) W =
        restrictIdeal (Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι)) W := by
  have : IsLocallyNoetherian (Blowup.strictTransform π Z H).subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformι_of_isLocallyNoetherian π Z H
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZ
    ((Blowup.strictTransform π Z H).subschemeι.base x) hxU
  have has : a ≠ s := by
    intro hasEq
    have hH' : restrictIdeal H U = c.coordIdeal {s} := by rw [hH, hasEq]
    have hbot := (blowupChartOfIsBlowup π c S hπ hZ s hs).strictTransform_subschemeι_preimage_domain_eq_bot
      Z H hs hZ hH'
    have hx0 : x ∈ (Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain := hmem
    rw [hbot] at hx0
    exact hx0
  obtain ⟨V, hVle, hVaff, hxV⟩ :=
    (blowupChartOfIsBlowup π c S hπ hZ s hs).exists_isAffineOpen_mem_le_domain
      ((Blowup.strictTransform π Z H).subschemeι.base x) hmem
  refine ⟨(Blowup.strictTransform π Z H).subschemeι ⁻¹ᵁ V, hxV, ?_⟩
  exact restrictIdeal_comap_strictTransform_eq_of_blowupChart ((blowupChartOfIsBlowup π c S hπ hZ s hs).restrict V hVle)
    hU hVaff Z H hs hZ a ha has hH D hDd q hq

/- English proof (authored)
The equality can be checked near every point of the strict transform of the hypersurface. Over the center, take a normal crossings chart. The hypersurface must be present since its strict transform contains the point upstairs. Its coordinate belongs to the center set by the ideal containment. The other divisor is absent or a distinct coordinate, so the affine blowup-chart comparison gives the local equality. Away from the center both strict transforms are total transforms and agree by the factorization. The local equalities give the sheaf equality.
-/
theorem comap_strictTransform_eq_strictTransform_of_comp_eq {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (q : (Blowup.strictTransform π Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.subschemeι = (Blowup.strictTransform π Z H).subschemeι ≫ π)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι =
      Blowup.strictTransform q (Z.comap H.subschemeι) (D.comap H.subschemeι) := by
  refine eq_of_locally_restrictIdeal_eq _ _ (fun x => ?_)
  by_cases hx : π.base ((Blowup.strictTransform π Z H).subschemeι.base x) ∈ Z.support
  · obtain ⟨U, hyU, hU, m, c, S, hZc, hcase⟩ :=
      exists_etaleChart_of_hasStrictNormalCrossingsWith p Z H E hsnc D hD
        (π.base ((Blowup.strictTransform π Z H).subschemeι.base x)) hx
    rcases hcase with hHtop | ⟨a, hH, hDd⟩
    · exact (false_of_mem_preimage_of_restrictIdeal_eq_top π Z H hπ c hZc hHtop x hyU).elim
    · exact exists_restrictIdeal_eq_of_mem_preimage π Z H hπ q hq D hU c hZc
        (mem_of_restrictIdeal_eq_coordIdeal_of_le hU c Z H S a hHZ hH hZc
          (π.base ((Blowup.strictTransform π Z H).subschemeι.base x)) hyU hx) hH hDd x hyU
  · exact exists_restrictIdeal_eq_of_notMem_support π Z H q hq D x hx

/- English proof (authored)
The chosen strict-transform lift has the required factorization through the original hypersurface. Apply the strict-transform comparison for any map with that factorization to this chosen lift.
-/
theorem comap_strictTransform_eq_strictTransformSubschemeLift {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap (Blowup.strictTransform π Z H).subschemeι =
      Blowup.strictTransform (strictTransformSubschemeLift π Z H) (Z.comap H.subschemeι) (D.comap H.subschemeι) :=
  comap_strictTransform_eq_strictTransform_of_comp_eq p π Z H E hsnc hHZ hπ
    (strictTransformSubschemeLift π Z H) (strictTransformSubschemeLift_comp_subschemeι π Z H) D hD

end FunctorialResolution.EmbeddedResolution

end
