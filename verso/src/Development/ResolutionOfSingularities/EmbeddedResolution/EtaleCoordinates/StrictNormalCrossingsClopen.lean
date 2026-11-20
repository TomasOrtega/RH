import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The unit ideal sheaf assigns the whole section ring as its ideal on each affine open.
-/
private theorem ideal_top {X : Scheme.{u}} (U : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal U = ⊤ := by simp

/- English proof (authored)
On V, the pulled-back ideal from U is obtained by ideal extension along the map of section rings. The product sheaf on U gives the product of the two section ideals, and ideal extension preserves products. This gives the product of the two extensions on V.
-/
private theorem ideal_comap_mul {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.affineOpens)
    (V : X.affineOpens) (e : (V : X.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) (I J : Y.IdealSheafData) :
    ((I * J).comap g).ideal V = (I.comap g).ideal V * (J.comap g).ideal V := by
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

/- English proof (authored)
Every point of the open subscheme V has image in V by definition of the inclusion. The preimage of V is therefore the whole open subscheme.
-/
private theorem top_le_ι_preimage_self {Y : Scheme.{u}} (V : Y.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (Opens.map V.ι.base).obj V := by
  intro x _
  exact x.2

/- English proof (authored)
A section on V viewed as an open of Y becomes a global section of the open subscheme V by the restriction identification. This direction is the inverse of the canonical isomorphism from global sections of the open subscheme to sections on V.
-/
private theorem ι_appLE_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appLE V ⊤ (top_le_ι_preimage_self V) = V.topIso.inv := by
  simp
  rfl

/- English proof (authored)
The section map is the inverse of the canonical section-ring isomorphism. In particular it is injective and surjective.
-/
private theorem ι_appLE_top_bijective {Y : Scheme.{u}} (V : Y.Opens) :
    Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) ∧
      Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) := by
  rw [ι_appLE_top_eq_topIso_inv]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective

/- English proof (authored)
Under the isomorphism between sections over V in Y and global sections of the open subscheme V, the ideal on V extends to the ideal of the restricted sheaf. By hypothesis that extension is the whole ring. Pulling the whole ring back along the isomorphism gives the whole section ring of V, so the ideal on V is the unit ideal.
-/
private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self V)
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (D.ideal ⟨V, hV⟩) = ⊤ := key.symm
  have hbij := ι_appLE_top_bijective V
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
        (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact hbij
  rw [key2, Ideal.comap_top] at hcomap
  exact hcomap.symm

/- English proof (authored)
In the algebra associated to the chart, its j-th coordinate is the image of the j-th polynomial variable. The chart's coordinate-ring map sends that variable to the pullback of the j-th affine-space coordinate, which is the coordinate section of the chart.
-/
private theorem etaleChartCoord_eq_coord {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} {m : ℕ} (c : EtaleChart p V m) (j : Fin m) :
    @etaleChartCoord k _ m Γ(X, V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]

/- English proof (authored)
On an affine neighbourhood of x, a section belongs to the prime corresponding to x exactly when its germ belongs to the maximal ideal of the local ring. The germ of the restricted section on V′ agrees with the original germ on V. Apply this criterion in both affine neighbourhoods to transfer membership.
-/
private theorem presheaf_map_mem_primeIdealOf {X : Scheme.{u}} {V V' : X.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (x : ↥X)
    (hxV : x ∈ V) (hxV' : x ∈ V') (s : Γ(X, V))
    (hs : s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :
    (X.presheaf.map (homOfLE hle).op).hom s ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
  have hres : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ V' x hxV'
      = X.presheaf.germ V x hxV := X.presheaf.germ_res (homOfLE hle) x hxV'
  have hgerm := congrArg
    (fun φ : Γ(X, V) ⟶ X.presheaf.stalk x => CommRingCat.Hom.hom φ s) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hgerm
  have h1 : X.presheaf.germ V x hxV s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (germ_mem_maximalIdeal_iff hV x hxV s).mpr hs
  refine (germ_mem_maximalIdeal_iff hV' x hxV' _).mp ?_
  show (X.presheaf.germ V' x hxV').hom ((X.presheaf.map (homOfLE hle).op).hom s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [hgerm]
  exact h1

/- English proof (authored)
Induct on the list of ideals. The empty list gives the unit ideal, generated by the empty product. For a nonempty list, shift the coordinate assignment by one position to apply induction to the tail. This gives a finite set of tail coordinates and a principal generator equal to their product.

The ideal of the pulled-back full product on V is the product of the pulled-back head ideal and tail ideal. An unassigned head gives the unit ideal and leaves the tail product as the generator. If the head is assigned a coordinate, its ideal on V is generated by that coordinate. Injectivity of the assignment prevents this coordinate from occurring in the tail set. Adjoin it, and multiply the two principal generators. Every index in the resulting set comes from an assigned list entry.
-/
private theorem exists_finset_comap_prod_ideal_eq_span_prod_coord {Y W : Scheme.{u}} {k : Type u}
    [Field k] {pY : Y ⟶ Spec (CommRingCat.of k)} (g : Y ⟶ W) (U : W.affineOpens) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : V ≤ g ⁻¹ᵁ (U : W.Opens)) {n : ℕ} (c : EtaleChart pY V n) :
    ∀ (F : List W.IdealSheafData) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ h : i < F.length, γ i = none → restrictIdeal ((F[i]'h).comap g) V = ⊤) →
      (∀ i, ∀ h : i < F.length, ∀ j, γ i = some j →
        restrictIdeal ((F[i]'h).comap g) V = c.coordIdeal {j}) →
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') →
      ∃ J : Finset (Fin n),
        (∀ j ∈ J, ∃ i, ∃ _ : i < F.length, γ i = some j) ∧
        (F.prod.comap g).ideal ⟨V, hV⟩ = Ideal.span {∏ j ∈ J, c.coord j} := by
  intro F
  induction F with
  | nil =>
      intro γ _ _ _
      refine ⟨∅, by simp, ?_⟩
      have h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData) := by
        rw [Blowup.idealSheafData_prod_nil]
        simp
      rw [h1, Finset.prod_empty, Ideal.span_singleton_one]
      exact ideal_top _
  | cons D F ih =>
      intro γ hnone hsome hinj
      have hlen : ∀ i, i < F.length → i + 1 < (D :: F).length := by
        intro i hi
        simp only [List.length_cons]
        omega
      have hD0 : (0 : ℕ) < (D :: F).length := by
        simp only [List.length_cons]
        omega
      obtain ⟨J', hJ'mem, hJ'⟩ := ih (fun i => γ (i + 1))
        (fun i h hg => hnone (i + 1) (hlen i h) hg)
        (fun i h j hg => hsome (i + 1) (hlen i h) j hg)
        (fun i i' hi hi' j h1 h2 => by
          have h3 := hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2
          omega)
      have hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩
          = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩ := by
        rw [Blowup.idealSheafData_prod_cons]
        exact ideal_comap_mul g U ⟨V, hV⟩ e D F.prod
      cases hγ0 : γ 0 with
      | none =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤ :=
            ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV (hnone 0 hD0 hγ0)
          refine ⟨J', ?_, ?_⟩
          · intro j hj
            obtain ⟨i, hi, hγi⟩ := hJ'mem j hj
            exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.top_mul]
      | some j0 =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0} := by
            have h2 := EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0}
              (hsome 0 hD0 j0 hγ0)
            rw [Finset.coe_singleton, Set.image_singleton] at h2
            exact h2
          have hj0 : j0 ∉ J' := by
            intro hj0mem
            obtain ⟨i, hi, hγi⟩ := hJ'mem j0 hj0mem
            have h3 := hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi
            omega
          refine ⟨insert j0 J', ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact ⟨0, hD0, hγ0⟩
            · obtain ⟨i, hi, hγi⟩ := hJ'mem j hj'
              exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton,
              Finset.prod_insert hj0]

/- English proof (authored)
Smoothness of the centre follows from its strict normal crossing charts. Its open subscheme T is therefore smooth over the field, so the local ring at y is regular. Choose the chart on T where each restricted divisor is either the unit ideal or generated by a distinct coordinate that vanishes at y. Choose an affine neighbourhood of the image of y in W and shrink the chart to a basic affine open V inside its inverse image. Restricting to V preserves the ideal descriptions, and the coordinate germs at y are the same as before.

The product of the pulled-back divisor ideals on V is generated by the product of the selected coordinates. Each selected coordinate lies in the prime of y. The ideal of their product is radical by the reducedness result for a product of distinct étale chart coordinates. The coordinate ring of V is nonzero because the point y gives a proper prime. In that ring distinct chart coordinates are different sections.

Extend the selected coordinate sections to sections whose germs form a regular system of parameters at y. Choose a parameter index representing each selected coordinate. Two selected coordinates with the same parameter index would be equal as sections, so the index choice is injective. The product of the selected coordinates is therefore the product of the corresponding subset of parameter sections. Taking the radical has no effect on this ideal. These sections and their selected indices give the required strict normal crossing witnesses.
-/
theorem strictNormalCrossingsRestrictToClopen : StrictNormalCrossingsRestrictToClopen.{u} := by
  intro k _ W p _ E Z hE hZ T hTclosed hcomp y
  have hsmZ : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hZ
  have hsmT : AlgebraicGeometry.Smooth (T.ι ≫ (Z.subschemeι ≫ p)) := inferInstance
  obtain ⟨V, hV, hyV, n, c, γ, hγ, hinjγ, hmem⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf_on_clopen p E hE Z hZ T hTclosed hcomp y
  obtain ⟨U, hyU, hU⟩ : ∃ U : W.Opens, (T.ι ≫ Z.subschemeι).base y ∈ U ∧ IsAffineOpen U := by
    obtain ⟨U, hUmem, hxU, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens W)
        (show (T.ι ≫ Z.subschemeι).base y ∈ (⊤ : W.Opens) from trivial)
    exact ⟨U, hxU, hUmem⟩
  have hyVU : y ∈ (V ⊓ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U : (T.toScheme).Opens) := ⟨hyV, hyU⟩
  obtain ⟨fs, hfle, hyf⟩ := hV.exists_basicOpen_le ⟨y, hyVU⟩ hyV
  obtain ⟨V', hV', hV'V, hV'U, hyV'⟩ :
      ∃ V' : (T.toScheme).Opens, IsAffineOpen V' ∧ V' ≤ V ∧
        V' ≤ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U ∧ y ∈ V' :=
    ⟨T.toScheme.basicOpen fs, hV.basicOpen fs, le_trans hfle inf_le_left,
      le_trans hfle inf_le_right, hyf⟩
  have hγ' : ∀ i, ∀ h : i < E.length,
      (γ i = none → restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V' = ⊤) ∧
      (∀ j, γ i = some j →
        restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V'
          = (c.restrict hV'V).coordIdeal {j}) := by
    intro i h
    refine ⟨fun hg => restrictIdeal_eq_top_of_le _ hV'V ((hγ i h).1 hg), fun j hg => ?_⟩
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c _ {j} ((hγ i h).2 j hg)
  obtain ⟨J₀, hJ₀mem, hJ₀⟩ :=
    exists_finset_comap_prod_ideal_eq_span_prod_coord (T.ι ≫ Z.subschemeι) ⟨U, hU⟩ hV' hV'U
      (c.restrict hV'V) E γ (fun i h => (hγ' i h).1) (fun i h => (hγ' i h).2) hinjγ
  have hJ₀prime : ∀ j ∈ J₀,
      (c.restrict hV'V).coord j ∈ (hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal := by
    intro j hj
    obtain ⟨i, hi, hγi⟩ := hJ₀mem j hj
    rw [FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hV'V j]
    exact presheaf_map_mem_primeIdealOf hV hV' hV'V y hyV hyV' (c.coord j) (hmem i hi j hγi)
  have hntr : Nontrivial ↥(T.toScheme.presheaf.obj (op V')) := by
    rcases subsingleton_or_nontrivial ↥(T.toScheme.presheaf.obj (op V')) with hs | hs
    · exfalso
      refine (hV'.primeIdealOf ⟨y, hyV'⟩).isPrime.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      have h10 : (1 : ↥(T.toScheme.presheaf.obj (op V'))) = 0 := @Subsingleton.elim _ hs 1 0
      rw [h10]
      exact Submodule.zero_mem _
    · exact hs
  have hcinj : Function.Injective (c.restrict hV'V).coord := by
    have h := @etaleChartCoord_injective k _ n ↥(T.toScheme.presheaf.obj (op V')) _
      (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') hntr
    intro a b hab
    refine h ?_
    simp only [etaleChartCoord_eq_coord]
    exact hab
  have hrad := @isRadical_span_singleton_prod_etaleChartCoord k _ n
    ↥(T.toScheme.presheaf.obj (op V')) _ (c.restrict hV'V).algebra
    ((c.restrict hV'V).algebra_etale hV') J₀
  simp only [etaleChartCoord_eq_coord] at hrad
  obtain ⟨N, f, hfcoord, hfreg⟩ :=
    exists_isRegularParameterSystem_with_coords_of_mem_prime hV' (c.restrict hV'V) y hyV'
      J₀ hJ₀prime
  choose ι hι using hfcoord
  have hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach,
      (fun j : { x // x ∈ J₀ } => ι j.1 j.2) a = (fun j : { x // x ∈ J₀ } => ι j.1 j.2) b →
        a = b := by
    intro a _ b _ hab
    have h1 : (c.restrict hV'V).coord a.1 = (c.restrict hV'V).coord b.1 := by
      rw [← hι a.1 a.2, ← hι b.1 b.2]
      exact congrArg f hab
    exact Subtype.ext (hcinj h1)
  have hprodJ : (∏ i ∈ J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), f i)
      = ∏ j ∈ J₀, (c.restrict hV'V).coord j := by
    rw [Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => (c.restrict hV'V).coord j)]
    exact Finset.prod_congr rfl fun j _ => hι j.1 j.2
  refine ⟨isRegularLocalRing_stalk_of_smooth (T.ι ≫ (Z.subschemeι ≫ p)) y,
    ⟨V', hV'⟩, hyV', N, f, J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), hfreg, ?_⟩
  rw [Scheme.IdealSheafData.radical_ideal, hJ₀, hrad.radical, hprodJ]

end FunctorialResolution.EmbeddedResolution

end
