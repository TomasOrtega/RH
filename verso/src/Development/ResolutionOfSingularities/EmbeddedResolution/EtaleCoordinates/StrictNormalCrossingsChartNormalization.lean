import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The filter can return j only from an original entry. It retains that entry exactly when its predicate is false. Thus the original entry is j and it fails the predicate.
-/
private theorem eq_some_and_not_of_bind_ite_eq_some {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n}
    (h : o.bind (fun j0 => if P j0 then none else some j0) = some j) : o = some j ∧ ¬ P j := by
  cases o with
  | none => simp at h
  | some j0 =>
    by_cases hb : P j0
    · simp [hb] at h
    · simp [hb] at h
      subst h
      exact ⟨rfl, hb⟩

/- English proof (authored)
The original entry is j. If the predicate were false at j, the filter would retain it. Since the result is empty, the predicate holds.
-/
private theorem of_bind_ite_eq_none {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n} (hg : o = some j)
    (h : o.bind (fun j0 => if P j0 then none else some j0) = none) : P j := by
  subst hg
  by_contra hb
  simp [hb] at h

/- English proof (authored)
An ideal sheaf is determined by its ideals on affine opens. The unit ideal sheaf assigns the whole section ring on each affine open, which agrees everywhere with the given sheaf.
-/
private theorem eq_top_of_forall_ideal_eq_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ W : X.affineOpens, I.ideal W = ⊤) : I = ⊤ := by
  have hfun : I.ideal = (⊤ : X.IdealSheafData).ideal := by
    funext W
    have htop : (⊤ : X.IdealSheafData).ideal W = ⊤ := rfl
    rw [h W, htop]
  exact Scheme.IdealSheafData.ext hfun

/- English proof (authored)
On the affine open U, the support of the ideal sheaf is the common zero locus of its section ideal. A section vanishes at x precisely when the basic open it defines misses x. Applying this to every section in the ideal gives the equivalence.
-/
private theorem mem_support_iff_forall_notMem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen f := by
  have h0 : x ∈ I.support ↔
      x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hx
  rw [h0, Scheme.mem_zeroLocus_iff]
  exact Iff.rfl

/- English proof (authored)
The affine identification takes x to its corresponding prime and takes the basic open of f to the basic open of the same ring element on the spectrum. A prime lies in this basic open precisely when it does not contain f.
-/
private theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (x : ↥U) :
    (x : ↥X) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  have h2 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
      (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) = (x : ↥X) :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf hU x
  have h1 : AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f
      = PrimeSpectrum.basicOpen f :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen hU f
  constructor
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x
        ∈ AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f := by
      show (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f
      rw [h2]
      exact hx
    rw [h1] at hmem
    exact (PrimeSpectrum.mem_basicOpen f _).mp hmem
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hx
    rw [← h1] at hmem
    have h3 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f := hmem
    rw [h2] at h3
    exact h3

/- English proof (authored)
Every section in the ideal on U is a multiple of g. The basic open of a multiple is contained in the basic open of g. Since x lies in none of these opens, it belongs to the common zero locus of the ideal, hence to its support.
-/
private theorem mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hg : x ∉ X.basicOpen g) : x ∈ I.support := by
  rw [mem_support_iff_forall_notMem_basicOpen I hU hx]
  intro f hf
  rw [hI, Ideal.mem_span_singleton] at hf
  obtain ⟨a, rfl⟩ := hf
  have hle : X.basicOpen (g * a) ≤ X.basicOpen g := by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  exact fun hc => hg (hle hc)

/- English proof (authored)
The generator g is a section in the ideal. Since x is in the support, this section vanishes there, so x lies outside its basic open. Under the affine identification that means the prime at x contains g.
-/
private theorem mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hs : x ∈ I.support) :
    g ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h := (mem_support_iff_forall_notMem_basicOpen I hU hx).mp hs g
    (by rw [hI]; exact Ideal.mem_span_singleton_self g)
  by_contra hc
  exact h ((mem_basicOpen_iff_notMem_primeIdealOf hU g ⟨x, hx⟩).mpr hc)

/- English proof (authored)
The image of the closed immersion defined by Z is the support of Z. In particular the image of z lies in that support.
-/
private theorem subschemeι_base_mem_support_of_subscheme {W : Scheme.{u}} (Z : W.IdealSheafData)
    (z : ↥Z.subscheme) : Z.subschemeι.base z ∈ Z.support := by
  have h : Z.subschemeι.base z ∈ Set.range Z.subschemeι.base := ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.range_subschemeι] at h

/- English proof (authored)
On any affine open of the open subscheme V, the restricted ideal is generated by the image of f. The section f is invertible on its basic open, and its restriction to V and then to the chosen affine open remains invertible. The extended principal ideal is therefore the whole section ring. These affine ideals determine the unit ideal sheaf.
-/
private theorem restrictIdeal_eq_top_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (I : X.IdealSheafData) (f : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {f}) {V : X.Opens} (hVb : V ≤ X.basicOpen f) :
    restrictIdeal I V = ⊤ := by
  have hbU : X.basicOpen f ≤ U := X.basicOpen_le f
  have hVU : V ≤ U := hVb.trans hbU
  rw [restrictIdeal_eq_comap_ι]
  refine eq_top_of_forall_ideal_eq_top _ ?_
  intro Wa
  have e : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ U := fun x _ => hVU x.2
  have e' : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ X.basicOpen f := fun x _ => hVb x.2
  rw [Scheme.IdealSheafData.comap_ideal_eq_span_image I V.ι ⟨U, hU⟩ Wa e {f} hI,
    Set.image_singleton, Ideal.span_singleton_eq_top]
  have hfac : V.ι.appLE U (Wa : (V.toScheme).Opens) e
      = X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e' := by
    rw [Scheme.Hom.map_appLE]
  have hcp : ((X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom) f
      = (V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom
          ((X.presheaf.map (homOfLE hbU).op).hom f) := rfl
  rw [hfac, hcp]
  exact IsUnit.map _ (X.toRingedSpace.isUnit_res_basicOpen f)

private def complOrderEmbInv (m : ℕ) (S : Finset (Fin m)) (t : Fin m) : Option (Fin (m - S.card)) :=
  if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h))

/- English proof (authored)
The partial inverse is undefined on indices in S. For any other index it returns that index's chosen position in the increasing enumeration of the complement.
-/
private theorem complInv_def (m : ℕ) (S : Finset (Fin m)) (t : Fin m) :
    complOrderEmbInv m S t =
      if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h)) :=
  rfl

/- English proof (authored)
If the partial inverse returns j, the original index is outside S and j is by construction a preimage under the complement enumeration. Conversely, if the enumeration sends j to t, then t is outside S. Its chosen preimage must be j by injectivity of the enumeration, so the partial inverse returns j.
-/
private theorem complInv_eq_some_iff (m : ℕ) (S : Finset (Fin m)) {t : Fin m}
    {j : Fin (m - S.card)} : complOrderEmbInv m S t = some j ↔ complOrderEmb m S j = t := by
  constructor
  · intro h
    by_cases ht : t ∈ S
    · rw [complInv_def, dif_pos ht] at h
      simp at h
    · rw [complInv_def, dif_neg ht] at h
      have hj : Classical.choose (exists_complOrderEmb_eq m S ht) = j := Option.some.inj h
      have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
      rw [hj] at hspec
      exact hspec
  · intro h
    have ht : t ∉ S := by
      rw [← h]
      exact complOrderEmb_notMem m S j
    rw [complInv_def, dif_neg ht]
    have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
    have heq : Classical.choose (exists_complOrderEmb_eq m S ht) = j :=
      (complOrderEmb m S).injective (by rw [hspec, h])
    rw [heq]

/- English proof (authored)
An empty original entry could not produce j. For an original entry t, the partial inverse returns j exactly when the complement enumeration sends j to t. Hence the original entry is the index at position j in that enumeration.
-/
private theorem eq_some_complOrderEmb_of_bind_complInv_eq_some (m : ℕ) (S : Finset (Fin m)) (o : Option (Fin m))
    (j : Fin (m - S.card)) (h : o.bind (complOrderEmbInv m S) = some j) :
    o = some (complOrderEmb m S j) := by
  cases o with
  | none => simp at h
  | some t =>
    have h' : complOrderEmbInv m S t = some j := h
    rw [(complInv_eq_some_iff m S).mp h']

/- English proof (authored)
If the original assignment contained an index, the hypothesis would put that index in the complement. The partial inverse is defined at every complementary index, so the result would contain an entry. Thus the original assignment was empty.
-/
private theorem eq_none_of_bind_complInv_eq_none (m : ℕ) (S : Finset (Fin m)) (o : Option (Fin m))
    (hnot : ∀ t, o = some t → t ∉ S) (h : o.bind (complOrderEmbInv m S) = none) : o = none := by
  cases o with
  | none => rfl
  | some t =>
    exfalso
    have h' : complOrderEmbInv m S t = none := h
    rw [complInv_def, dif_neg (hnot t rfl)] at h'
    simp at h'

section

variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}

/- English proof (authored)
After the original chart and its affine-space projection, the map from V to the spectrum of k is its inclusion followed by p. Precompose this identity with the restriction of f. The square of open restrictions identifies its composite with the inclusion of the inverse-image open followed by f and p.
-/
theorem morphismRestrict_comp_map_comp_affineSpaceFinToSpec (c : EtaleChart p V n) (f : Y' ⟶ Y)
    [IsOpenImmersion f] :
    (morphismRestrict f V ≫ c.map) ≫ affineSpaceFinToSpec k n = (f ⁻¹ᵁ V).ι ≫ (f ≫ p) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]

/- English proof (authored)
Restricting the open immersion f to the inverse image of V gives an open immersion into V. It is étale, and the original chart is étale. Their composite is therefore étale.
-/
theorem etale_morphismRestrict_comp_map (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f] :
    Etale (morphismRestrict f V ≫ c.map) := by
  have h0 : IsOpenImmersion (morphismRestrict f V ≫ V.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  have h1 : IsOpenImmersion (morphismRestrict f V) :=
    IsOpenImmersion.of_comp (morphismRestrict f V) V.ι
  have h2 : Etale c.map := c.isEtale
  have h3 : Etale (morphismRestrict f V) := inferInstance
  infer_instance

def EtaleChart.pullbackOpenImmersion (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f] :
    EtaleChart (f ≫ p) (f ⁻¹ᵁ V) n :=
  ⟨morphismRestrict f V ≫ c.map, morphismRestrict_comp_map_comp_affineSpaceFinToSpec c f,
    etale_morphismRestrict_comp_map c f⟩

/- English proof (authored)
The pulled-back chart uses the map from the inverse-image open to V followed by the original chart map. This is its defining underlying map.
-/
theorem EtaleChart.pullbackOpenImmersion_map (c : EtaleChart p V n) (f : Y' ⟶ Y)
    [IsOpenImmersion f] :
    (c.pullbackOpenImmersion f).map = morphismRestrict f V ≫ c.map :=
  rfl

/- English proof (authored)
The coordinate ideal of the pulled-back chart is the pullback of the original chart ideal along the restricted map to V, because both are defined from the same coordinate subspace ideal. By hypothesis the original chart ideal equals the restriction of D. Pullback of that restriction agrees with restriction of the pulled-back ideal because the square of open restrictions commutes.
-/
private theorem restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion (c : EtaleChart p V n)
    (f : Y' ⟶ Y) [IsOpenImmersion f] (D : Y.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal D V = c.coordIdeal S) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = (c.pullbackOpenImmersion f).coordIdeal S := by
  have h1 : (c.pullbackOpenImmersion f).coordIdeal S
      = (c.coordIdeal S).comap (morphismRestrict f V) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal,
      EtaleChart.pullbackOpenImmersion_map, Scheme.IdealSheafData.comap_comp]
  rw [h1, ← h, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]

end

/- English proof (authored)
Restricting the pullback to the inverse-image open is the same as pulling back the restriction to V. That restriction is the unit ideal by hypothesis, and its pullback is the unit ideal.
-/
theorem restrictIdeal_comap_preimage_eq_top {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (V : Y.Opens)
    (D : Y.IdealSheafData) (h : restrictIdeal D V = ⊤) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = ⊤ := by
  have h1 : restrictIdeal (D.comap f) (f ⁻¹ᵁ V)
      = (restrictIdeal D V).comap (morphismRestrict f V) := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
  rw [h1, h, Scheme.IdealSheafData.comap_top]

/- English proof (authored)
Every open neighbourhood of a point of A meets A. Irreducibility says that such a neighbourhood and O have a common point in A, since O also meets A. Hence A lies in the closure of its intersection with O. The inverse image of the closed set C under the continuous map g is closed and contains that intersection, so it contains A. This gives the claimed inclusion of images.
-/
theorem image_subset_of_image_inter_subset {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {A O : Set α} {g : α → β} {C : Set β} (hA : IsIrreducible A)
    (hO : IsOpen O) (hAO : (A ∩ O).Nonempty) (hg : Continuous g) (hC : IsClosed C)
    (h : g '' (A ∩ O) ⊆ C) : g '' A ⊆ C := by
  have hsub : A ⊆ closure (A ∩ O) := by
    intro x hx
    rw [mem_closure_iff]
    intro u hu hxu
    obtain ⟨z, hz⟩ := hA.2 u O hu hO ⟨x, hx, hxu⟩ hAO
    exact ⟨z, hz.2.1, hz.1, hz.2.2⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : g x ∈ g '' closure (A ∩ O) := ⟨x, hsub hx, rfl⟩
  exact closure_minimal h hC (image_closure_subset_closure_image hg h1)

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}

/- English proof (authored)
Let t be the product of the chart coordinates outside the prime at y. Since the complement of the prime is multiplicatively closed, t stays outside it, and its affine basic open still contains y. Restrict the chart to this open. Every coordinate appearing in t is invertible there because each is a factor of the product being inverted.

Delete from the assignment every coordinate outside the prime. An originally unassigned ideal is still the unit ideal after restriction. An ideal whose coordinate was deleted is now the unit ideal because that generator became invertible. For retained coordinates the coordinate-ideal description persists under restriction. The assignment remains injective because the retained values are a subset of the old ones.

Finally, any retained coordinate belongs to the original prime and hence vanishes at y. The corresponding ideal has y in its support. On the smaller affine open it is again generated by the restricted coordinate, so the support criterion puts this generator in the prime at y there.
-/
theorem exists_etaleChart_coord_mem_primeIdealOf (F : List X.IdealSheafData) (y : ↥X) (U : X.Opens)
    (hU : IsAffineOpen U) (hyU : y ∈ U) {n : ℕ} (c : EtaleChart p U n) (γ : ℕ → Option (Fin n))
    (hdesc : ∀ i, ∀ hi : i < F.length,
      (γ i = none → restrictIdeal (F[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal (F[i]'hi) U = c.coordIdeal {j})
    (hinj : ∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (hy' : y ∈ U') (n' : ℕ)
      (c' : EtaleChart p U' n') (γ' : ℕ → Option (Fin n')),
      (∀ i, ∀ hi : i < F.length,
        (γ' i = none → restrictIdeal (F[i]'hi) U' = ⊤) ∧
          ∀ j, γ' i = some j → restrictIdeal (F[i]'hi) U' = c'.coordIdeal {j}) ∧
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ' i = some j → γ' i' = some j → i = i') ∧
      (∀ i, i < F.length → ∀ j, γ' i = some j →
        c'.coord j ∈ (hU'.primeIdealOf ⟨y, hy'⟩).asIdeal) := by
  classical
  set notInPrime : Finset (Fin n) :=
    Finset.univ.filter (fun j => c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) with hBadDef
  have hBad : ∀ j : Fin n, j ∈ notInPrime ↔ c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    intro j
    rw [hBadDef]
    simp
  set t : Γ(X, U) := ∏ j ∈ notInPrime, c.coord j with htdef
  have ht : t ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    have hmem : ∀ j ∈ notInPrime, c.coord j ∈ Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
      fun j hj => (hBad j).mp hj
    have hprod := Submonoid.prod_mem (Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) hmem
    rw [← htdef] at hprod
    exact hprod
  have hUt : IsAffineOpen (X.basicOpen t) := hU.basicOpen t
  have hle : X.basicOpen t ≤ U := X.basicOpen_le t
  have hy' : y ∈ X.basicOpen t := (mem_basicOpen_iff_notMem_primeIdealOf hU t ⟨y, hyU⟩).mpr ht
  have hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j) := by
    intro j hj
    have hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i := by
      rw [htdef]
      exact (Finset.mul_prod_erase notInPrime (fun i => c.coord i) hj).symm
    rw [hsplit, Scheme.basicOpen_mul]
    exact inf_le_left
  refine ⟨X.basicOpen t, hUt, hy', n, c.restrict hle,
    fun i => (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0), ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hA, hB⟩ := hdesc i hi
    constructor
    · intro hnone
      have hnone' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = none := hnone
      by_cases hg : γ i = none
      · exact restrictIdeal_eq_top_of_le _ hle (hA hg)
      · obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hg
        have hb : j0 ∈ notInPrime := of_bind_ite_eq_none (fun j1 => j1 ∈ notInPrime) hj0 hnone'
        have hideal : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j0} := by
          rw [c.ideal_eq_span_coord hU _ _ (hB j0 hj0), Finset.coe_singleton,
            Set.image_singleton]
        exact restrictIdeal_eq_top_of_le_basicOpen hU _ (c.coord j0) hideal (hbasic_le j0 hb)
    · intro j hj
      have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
      obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)
  · intro i i' hi hi' j hj hj'
    have hja : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    have hjb : (γ i').bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj'
    exact hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hja).1
      (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hjb).1
  · intro i hi j hj
    obtain ⟨_, hB⟩ := hdesc i hi
    have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
    have hmemP : c.coord j ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      by_contra hcon
      exact hb ((hBad j).mpr hcon)
    have hidU : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j} := by
      rw [c.ideal_eq_span_coord hU _ _ (hB j hg), Finset.coe_singleton, Set.image_singleton]
    have hynb : y ∉ X.basicOpen (c.coord j) := fun hc =>
      (mem_basicOpen_iff_notMem_primeIdealOf hU (c.coord j) ⟨y, hyU⟩).mp hc hmemP
    have hysup : y ∈ (F[i]'hi).support :=
      mem_support_of_ideal_eq_span_singleton _ hU hyU (c.coord j) hidU hynb
    have hidU' : (F[i]'hi).ideal ⟨X.basicOpen t, hUt⟩
        = Ideal.span {(c.restrict hle).coord j} := by
      rw [(c.restrict hle).ideal_eq_span_coord hUt _ _
        (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)), Finset.coe_singleton,
        Set.image_singleton]
    exact mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton _ hUt hy' _ hidU' hysup

end

section

variable {W : Scheme.{u}} {k : Type u} [Field k]

/- English proof (authored)
Take a common strict normal crossing chart for the centre Z and the divisors at the image of y, and shrink to an affine neighbourhood. Let S be the coordinates cutting out the centre. Suppose a divisor is assigned a coordinate in S. Its ideal is then contained in the ideal of Z on this neighbourhood, so every point of Z there lies in the divisor support. In particular this holds for the image of the part of the irreducible component of T through y lying over the neighbourhood. That part is nonempty and open in the component. Its image lying in the closed support forces the whole component's image into that support by irreducibility and continuity. This contradicts the component hypothesis. Every assigned divisor coordinate is therefore outside S.

Restrict the chart to the closed subscheme by keeping the complementary coordinates. Pull this chart back along the open inclusion of T, then shrink to an affine neighbourhood of y. For the divisor list, translate each assigned complementary coordinate to its position in the new chart and leave each unassigned entry empty. The singleton ideal formula identifies assigned divisors with the new coordinate ideals, and the unit ideal remains the unit ideal under pullback and restriction. Distinctness of assigned coordinates follows from distinctness in the original chart and the bijection with the complement.
-/
theorem exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith (q : W ⟶ Spec (CommRingCat.of k))
    (E : List W.IdealSheafData) (Z : W.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z E)
    (T : Z.subscheme.Opens)
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') := by
  classical
  have hbase : ∀ z : ↥T.toScheme,
      (T.ι ≫ Z.subschemeι).base z = Z.subschemeι.base (T.ι.base z) := fun _ => rfl
  have hcont : Continuous fun z : ↥T.toScheme => (T.ι ≫ Z.subschemeι).base z :=
    (T.ι ≫ Z.subschemeι).base.hom.continuous
  have hw : Z.subschemeι.base (T.ι.base y) ∈ Z.support := subschemeι_base_mem_support_of_subscheme Z _
  obtain ⟨U, hwU, m, c, a, S, hainj, hanone, hasome, hZU⟩ := hZ.exists_etaleChart hw
  obtain ⟨U₀, hU₀aff, hwU₀, hU₀le⟩ := exists_isAffineOpen_mem_and_subset hwU
  have hZU₀ : restrictIdeal Z U₀ = (c.restrict hU₀le).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c Z S hZU
  have hE₀none : ∀ (i : ℕ) (hi : i < E.length), a i = none →
      restrictIdeal (E[i]'hi) U₀ = ⊤ := fun i hi h =>
    restrictIdeal_eq_top_of_le _ hU₀le (hanone i hi h)
  have hE₀some : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal (E[i]'hi) U₀ = (c.restrict hU₀le).coordIdeal {t} := fun i hi t h =>
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c _ _ (hasome i hi t h)
  have hnotS : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t → t ∉ S := by
    intro i hi t hat htS
    have hEle : (E[i]'hi).ideal ⟨U₀, hU₀aff⟩ ≤ Z.ideal ⟨U₀, hU₀aff⟩ := by
      rw [(c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ (hE₀some i hi t hat),
        (c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ hZU₀,
        Finset.coe_singleton, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨t, Finset.mem_coe.mpr htS, rfl⟩
    refine hcomp (E[i]'hi) (List.getElem_mem hi) (irreducibleComponent y)
      (irreducibleComponent_mem_irreducibleComponents y) ?_
    refine image_subset_of_image_inter_subset isIrreducible_irreducibleComponent
      (U₀.2.preimage hcont) ⟨y, mem_irreducibleComponent, ?_⟩ hcont
      (E[i]'hi).support.2 ?_
    · show (T.ι ≫ Z.subschemeι).base y ∈ (U₀ : Set ↥W)
      rw [hbase y]
      exact hwU₀
    · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      have hzU₀ : (T.ι ≫ Z.subschemeι).base z ∈ U₀ := hz
      have hzZ : (T.ι ≫ Z.subschemeι).base z ∈ Z.support := by
        rw [hbase z]
        exact subschemeι_base_mem_support_of_subscheme Z _
      exact (mem_support_iff_forall_notMem_basicOpen _ hU₀aff hzU₀).mpr
        (fun f hf => (mem_support_iff_forall_notMem_basicOpen Z hU₀aff hzU₀).mp hzZ f (hEle hf))
  have hyV : y ∈ T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀) := hwU₀
  obtain ⟨U₁, hU₁aff, hyU₁, hU₁le⟩ := exists_isAffineOpen_mem_and_subset hyV
  set d := (c.restrict hU₀le).restrictToSubscheme hU₀aff Z S hZU₀ with hd
  set d' := d.pullbackOpenImmersion T.ι with hd'
  refine ⟨U₁, hU₁aff, hyU₁, m - S.card, d'.restrict hU₁le,
    fun i => (a i).bind (complOrderEmbInv m S), ?_, ?_⟩
  · intro i hi
    constructor
    · intro hnone
      have hnone' : (a i).bind (complOrderEmbInv m S) = none := hnone
      have ha : a i = none :=
        eq_none_of_bind_complInv_eq_none m S (a i) (fun t ht => hnotS i hi t ht) hnone'
      have h1 := hE₀none i hi ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀) = ⊤ :=
        restrictIdeal_comap_subschemeι_eq_top Z U₀ _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top T.ι _ _ h2
      have h4 := restrictIdeal_eq_top_of_le _ hU₁le h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
    · intro j hj
      have hj' : (a i).bind (complOrderEmbInv m S) = some j := hj
      have ha : a i = some (complOrderEmb m S j) := eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hj'
      have h1 := hE₀some i hi _ ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀)
          = d.coordIdeal {j} :=
        (c.restrict hU₀le).restrictToSubscheme_coordIdeal_singleton hU₀aff Z S hZU₀ j _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = d'.coordIdeal {j} :=
        restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion d T.ι _ _ h2
      have h4 := restrictIdeal_eq_restrict_coordIdeal_of_le hU₁le d' _ _ h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
  · intro i i' hi hi' j hj hj'
    have hja : (a i).bind (complOrderEmbInv m S) = some j := hj
    have hjb : (a i').bind (complOrderEmbInv m S) = some j := hj'
    exact hainj i hi i' hi' (complOrderEmb m S j) (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hja)
      (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i') j hjb)

/- English proof (authored)
First construct the chart on T using the component condition. Regard the divisors as the list of ideals pulled back to T, preserving their positions. Apply the chart normalization at y to this list. It supplies an affine chart with the same two alternatives for each ideal and with every assigned coordinate in the prime at y. Expressing each entry again as the pullback of the corresponding original divisor gives the stated witnesses.
-/
theorem exists_etaleChart_coord_mem_primeIdealOf_on_clopen (q : W ⟶ Spec (CommRingCat.of k)) [Smooth q]
    (E : List W.IdealSheafData) (_hE : InStrictNormalCrossingPosition q E) (Z : W.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith q Z E) (T : Z.subscheme.Opens)
    (_hTclosed : IsClosed (T : Set ↥Z.subscheme))
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') ∧
      (∀ i, i < E.length → ∀ j, γ i = some j → c.coord j ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨U, hU, hy, n, c, γ, hdesc, hinj⟩ :=
    exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith q E Z hZ T hcomp y
  have hlen : (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length
      = E.length := by
    simp
  have hdesc' : ∀ i, ∀ hi : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length,
      (γ i = none → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = c.coordIdeal {j} := by
    intro i hi
    have hi' : i < E.length := by rwa [hlen] at hi
    obtain ⟨hA, hB⟩ := hdesc i hi'
    simp only [List.getElem_map]
    exact ⟨hA, hB⟩
  have hinj' : ∀ i i', i < (E.map fun D : W.IdealSheafData =>
      D.comap (T.ι ≫ Z.subschemeι)).length →
      i' < (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length →
      ∀ j, γ i = some j → γ i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    rw [hlen] at hi hi'
    exact hinj i i' hi hi' j h1 h2
  obtain ⟨U', hU', hy', n', c', γ', h1, h2, h3⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf
      (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)) y U hU hy c γ
      hdesc' hinj'
  refine ⟨U', hU', hy', n', c', γ', ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length := by
      rw [hlen]; exact hi
    obtain ⟨hA, hB⟩ := h1 i hi'
    simp only [List.getElem_map] at hA hB
    exact ⟨hA, hB⟩
  · intro i i' hi hi' j hj hj'
    exact h2 i i' (by rw [hlen]; exact hi) (by rw [hlen]; exact hi') j hj hj'
  · intro i hi j hj
    exact h3 i (by rw [hlen]; exact hi) j hj

end

end FunctorialResolution.EmbeddedResolution
