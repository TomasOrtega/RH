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

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ideal_top {X : Scheme.{u}} (U : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal U = ⊤ := by simp

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e, Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e, Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]`.
-/
private theorem ideal_comap_mul {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.affineOpens)
    (V : X.affineOpens) (e : (V : X.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) (I J : Y.IdealSheafData) :
    ((I * J).comap g).ideal V = (I.comap g).ideal V * (J.comap g).ideal V := by
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

/- English proof (translation)
Introduce `x _`. Conclude with `x.2`.
-/
private theorem top_le_ι_preimage_self {Y : Scheme.{u}} (V : Y.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (Opens.map V.ι.base).obj V := by
  intro x _
  exact x.2

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem ι_appLE_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appLE V ⊤ (top_le_ι_preimage_self V) = V.topIso.inv := by
  simp
  rfl

/- English proof (translation)
Rewrite using `[ι_appLE_top_eq_topIso_inv]`. Conclude with `V.topIso.commRingCatIsoToRingEquiv.symm.bijective`.
-/
private theorem ι_appLE_top_bijective {Y : Scheme.{u}} (V : Y.Opens) :
    Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) ∧
      Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) := by
  rw [ι_appLE_top_eq_topIso_inv]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `key` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self V)`. Rewrite `key` using `[← restrictIdeal_eq_comap_ι, htop]`. Establish `h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤`. Simplify using the standard rewrite rules.

Rewrite `key` using `[h0]`. Establish `key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (D.ideal ⟨V, hV⟩) = ⊤` using `key.symm`. Establish `hbij` using `ι_appLE_top_bijective V`. Establish `hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩`. Apply `Ideal.comap_map_of_bijective` to reduce the goal to its premises.

Conclude with `hbij`. Rewrite `hcomap` using `[key2, Ideal.comap_top]`. Conclude with `hcomap.symm`.
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

/- English proof (translation)
Rewrite using `[etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]`.
-/
private theorem etaleChartCoord_eq_coord {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} {m : ℕ} (c : EtaleChart p V m) (j : Fin m) :
    @etaleChartCoord k _ m Γ(X, V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]

/- English proof (translation)
Establish `hres : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ V' x hxV' = X.presheaf.germ V x hxV` using `X.presheaf.germ_res (homOfLE hle) x hxV'`. Establish `hgerm` using `congrArg (fun φ : Γ(X, V) ⟶ X.presheaf.stalk x => CommRingCat.Hom.hom φ s) hres`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at hgerm`. Establish `h1 : X.presheaf.germ V x hxV s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)` using `(germ_mem_maximalIdeal_iff hV x hxV s).mpr hs`. Use `(germ_mem_maximalIdeal_iff hV' x hxV' _).mp ?_` and prove the remaining obligations.

Use `show (X.presheaf.germ V' x hxV').hom ((X.presheaf.map (homOfLE hle).op).hom s) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)`. Rewrite using `[hgerm]`. Conclude with `h1`.
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

/- English proof (translation)
Introduce `F`. Proceed by induction on `F with`. Consider the case `nil`. Introduce `γ _ _ _`. Use `⟨∅, by simp, ?_⟩` and prove the remaining obligations.

Establish `h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData)`. Rewrite using `[Blowup.idealSheafData_prod_nil]`. Simplify using the standard rewrite rules. Rewrite using `[h1, Finset.prod_empty, Ideal.span_singleton_one]`. Conclude with `ideal_top _`.

Consider the case `cons D F ih`. Introduce `γ hnone hsome hinj`. Establish `hlen : ∀ i, i < F.length → i + 1 < (D :: F).length`. Introduce `i hi`. Simplify using `only [List.length_cons]`.

Use linear arithmetic over natural numbers and integers. Establish `hD0 : (0 : ℕ) < (D :: F).length`. Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers. Take `⟨J', hJ'mem, hJ'⟩` from `ih (fun i => γ (i + 1)) (fun i h hg => hnone (i + 1) (hlen i h) hg) (fun i h j hg => hsome (i + 1) (hlen i h) j hg) (fun i i' hi hi' j h1 h2 => by`.

Establish `h3` using `hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2`. Use the proof step `omega)`. Establish `hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩ = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩`. Rewrite using `[Blowup.idealSheafData_prod_cons]`. Conclude with `ideal_comap_mul g U ⟨V, hV⟩ e D F.prod`.

Consider the cases of `hγ0 : γ 0 with`. Consider the case `none`. Establish `hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤` using `ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV (hnone 0 hD0 hγ0)`. Use `⟨J', ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`.

Take `⟨i, hi, hγi⟩` from `hJ'mem j hj`. Conclude with `⟨i + 1, hlen i hi, hγi⟩`. Rewrite using `[hprod, hD, hJ', Ideal.top_mul]`. Consider the case `some j0`. Establish `hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0}`.

Establish `h2` using `EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0} (hsome 0 hD0 j0 hγ0)`. Rewrite `h2` using `[Finset.coe_singleton, Set.image_singleton]`. Conclude with `h2`. Establish `hj0 : j0 ∉ J'`. Introduce `hj0mem`.

Take `⟨i, hi, hγi⟩` from `hJ'mem j0 hj0mem`. Establish `h3` using `hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi`. Use linear arithmetic over natural numbers and integers. Use `⟨insert j0 J', ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`.

Break down `Finset.mem_insert.mp hj with rfl | hj'` into its components or cases. Conclude with `⟨0, hD0, hγ0⟩`. Take `⟨i, hi, hγi⟩` from `hJ'mem j hj'`. Conclude with `⟨i + 1, hlen i hi, hγi⟩`. Rewrite using `[hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton, Finset.prod_insert hj0]`.
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

/- English proof (translation)
Introduce `k _ W p _ E Z hE hZ T hTclosed hcomp y`. Establish `hsmZ : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)` using `smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith Z E hZ`. Establish `hsmT : AlgebraicGeometry.Smooth (T.ι ≫ (Z.subschemeι ≫ p))` using `inferInstance`. Take `⟨V, hV, hyV, n, c, γ, hγ, hinjγ, hmem⟩` from `exists_etaleChart_coord_mem_primeIdealOf_on_clopen p E hE Z hZ T hTclosed hcomp y`. Choose the witnesses or unpack the hypotheses as in `⟨U, hyU, hU⟩ : ∃ U : W.Opens, (T.ι ≫ Z.subschemeι).base y ∈ U ∧ IsAffineOpen U := by`.

Take `⟨U, hUmem, hxU, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens W) (show (T.ι ≫ Z.subschemeι).base y ∈ (⊤ : W.Opens) from trivial)`. Conclude with `⟨U, hxU, hUmem⟩`. Establish `hyVU : y ∈ (V ⊓ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U : (T.toScheme).Opens)` using `⟨hyV, hyU⟩`. Take `⟨fs, hfle, hyf⟩` from `hV.exists_basicOpen_le ⟨y, hyVU⟩ hyV`. Take `⟨V', hV', hV'V, hV'U, hyV'⟩ : ∃ V' : (T.toScheme).Opens, IsAffineOpen V' ∧ V' ≤ V ∧ V' ≤ (T.ι ≫ Z.subschemeι) ⁻¹ᵁ U ∧ y ∈ V'` from `⟨T.toScheme.basicOpen fs, hV.basicOpen fs, le_trans hfle inf_le_left, le_trans hfle inf_le_right, hyf⟩`.

Establish `hγ' : ∀ i, ∀ h : i < E.length, (γ i = none → restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V' = ⊤) ∧ (∀ j, γ i = some j → restrictIdeal ((E[i]'h).comap (T.ι ≫ Z.subschemeι)) V' = (c.restrict hV'V).coordIdeal {j})`. Introduce `i h`. Use `⟨fun hg => restrictIdeal_eq_top_of_le _ hV'V ((hγ i h).1 hg), fun j hg => ?_⟩` and prove the remaining obligations. Conclude with `restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c _ {j} ((hγ i h).2 j hg)`. Take `⟨J₀, hJ₀mem, hJ₀⟩` from `exists_finset_comap_prod_ideal_eq_span_prod_coord (T.ι ≫ Z.subschemeι) ⟨U, hU⟩ hV' hV'U (c.restrict hV'V) E γ (fun i h => (hγ' i h).1) (fun i h => (hγ' i h).2) hinjγ`.

Establish `hJ₀prime : ∀ j ∈ J₀, (c.restrict hV'V).coord j ∈ (hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal`. Introduce `j hj`. Take `⟨i, hi, hγi⟩` from `hJ₀mem j hj`. Rewrite using `[FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hV'V j]`. Conclude with `presheaf_map_mem_primeIdealOf hV hV' hV'V y hyV hyV' (c.coord j) (hmem i hi j hγi)`.

Establish `hntr : Nontrivial ↥(T.toScheme.presheaf.obj (op V'))`. Break down `subsingleton_or_nontrivial ↥(T.toScheme.presheaf.obj (op V')) with hs | hs` into its components or cases. It suffices to derive a contradiction. Use `(hV'.primeIdealOf ⟨y, hyV'⟩).isPrime.ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `h10 : (1 : ↥(T.toScheme.presheaf.obj (op V'))) = 0` using `@Subsingleton.elim _ hs 1 0`. Rewrite using `[h10]`. Conclude with `Submodule.zero_mem _`. Conclude with `hs`. Establish `hcinj : Function.Injective (c.restrict hV'V).coord`.

Establish `h` using `@etaleChartCoord_injective k _ n ↥(T.toScheme.presheaf.obj (op V')) _ (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') hntr`. Introduce `a b hab`. Use `h ?_` and prove the remaining obligations. Simplify using `only [etaleChartCoord_eq_coord]`. Conclude with `hab`.

Establish `hrad` using `@isRadical_span_singleton_prod_etaleChartCoord k _ n ↥(T.toScheme.presheaf.obj (op V')) _ (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') J₀`. Simplify using `only [etaleChartCoord_eq_coord] at hrad`. Take `⟨N, f, hfcoord, hfreg⟩` from `exists_isRegularParameterSystem_with_coords_of_mem_prime hV' (c.restrict hV'V) y hyV' J₀ hJ₀prime`. Use `choose ι hι using hfcoord`. Establish `hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach, (fun j : { x // x ∈ J₀ } => ι j.1 j.2) a = (fun j : { x // x ∈ J₀ } => ι j.1 j.2) b → a = b`.

Introduce `a _ b _ hab`. Establish `h1 : (c.restrict hV'V).coord a.1 = (c.restrict hV'V).coord b.1`. Rewrite using `[← hι a.1 a.2, ← hι b.1 b.2]`. Conclude with `congrArg f hab`. Conclude with `Subtype.ext (hcinj h1)`.

Establish `hprodJ : (∏ i ∈ J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), f i) = ∏ j ∈ J₀, (c.restrict hV'V).coord j`. Rewrite using `[Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => (c.restrict hV'V).coord j)]`. Conclude with `Finset.prod_congr rfl fun j _ => hι j.1 j.2`. Use `⟨isRegularLocalRing_stalk_of_smooth (T.ι ≫ (Z.subschemeι ≫ p)) y, ⟨V', hV'⟩, hyV', N, f, J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), hfreg, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.radical_ideal, hJ₀, hrad.radical, hprodJ]`.
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
