import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}

/- English proof (authored)
The supremum condition means that the opens cover the source. Smoothness is local on the source in the Zariski topology. Since the restriction to each member of this cover is smooth, the map is smooth.
-/
theorem smooth_of_iSup_eq_top {W Y : Scheme.{u}} (f : W ⟶ Y) {ι : Sort*} (U : ι → W.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, Smooth ((U i).ι ≫ f)) : Smooth f := by
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have hVtop : (⨆ i : PLift ι, U i.down) = ⊤ := by
    rw [← hU]
    exact le_antisymm (iSup_le fun i => le_iSup U i.down)
      (iSup_le fun i => le_iSup (fun j : PLift ι => U j.down) (PLift.up i))
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun i : PLift ι => U i.down) hVtop).mpr
    fun i => h i.down

/- English proof (authored)
Restriction of Z to V is obtained by pulling its restriction to U back along the inclusion of V in U. On U that ideal is itself the pullback of the coordinate subspace ideal along the chart. Thus the restriction to V is the pullback along the composite defining the restricted chart.
-/
theorem restrictIdeal_eq_restrict_coordIdeal_of_le {U V : X.Opens} (hVU : V ≤ U) (c : EtaleChart p U m)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal Z V = (c.restrict hVU).coordIdeal S := by
  have h' : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]

/- English proof (authored)
Pull back the restriction of Z on U along the inclusion of V. By hypothesis it is the unit ideal, and pullback of the unit ideal is again the unit ideal.
-/
theorem restrictIdeal_eq_top_of_le {Y : Scheme.{u}} (Z : Y.IdealSheafData) {U V : Y.Opens}
    (hVU : V ≤ U) (h : restrictIdeal Z U = ⊤) : restrictIdeal Z V = ⊤ := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal Z hVU, h, Scheme.IdealSheafData.comap_top]

/- English proof (authored)
The chart restricts to an étale chart on the part of the closed subscheme over U. Setting the coordinates indexed by S to zero reduces the target to affine space of dimension m minus the number of those coordinates. The structure map of the closed subscheme on this open is the composite of that étale map with the smooth affine-space projection. Both maps are smooth, so the composite is smooth.
-/
theorem smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Smooth ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) := by
  have hsm : Smooth (affineSpaceFinToSpec k (m - S.card)) := affineSpaceIsSmooth ..
  have het : Etale (c.restrictToSubscheme hU Z S h).map :=
    (c.restrictToSubscheme hU Z S h).isEtale
  have hsm2 : Smooth (c.restrictToSubscheme hU Z S h).map := inferInstance
  have hc : (c.restrictToSubscheme hU Z S h).map ≫ affineSpaceFinToSpec k (m - S.card)
      = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p) :=
    (c.restrictToSubscheme hU Z S h).comp_struct
  rw [← hc]
  infer_instance

/- English proof (authored)
Each point of the closed subscheme maps into the support of Z. At its image choose the neighbourhood and chart supplied by the hypothesis. Shrink the neighbourhood to an affine open containing that image. The equality of ideals persists for the restricted chart. The preceding chart result gives smoothness on the inverse image of this affine open in the closed subscheme. These inverse images cover the subscheme, so smoothness holds globally by locality.
-/
theorem smooth_subschemeι_comp_of_locally_eq_coordIdeal (Z : X.IdealSheafData)
    (h : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S) :
    Smooth (Z.subschemeι ≫ p) := by
  classical
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have key : ∀ y : ↥Z.subscheme, ∃ W : (Z.subscheme).Opens,
      y ∈ W ∧ Smooth (W.ι ≫ (Z.subschemeι ≫ p)) := by
    intro y
    have hy : Z.subschemeι.base y ∈ Z.support := by
      have hmem : Z.subschemeι.base y ∈ Set.range Z.subschemeι.base := Set.mem_range_self y
      simpa using hmem
    obtain ⟨U, hxU, n, c, S, hS⟩ := h _ hy
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
    have hV' : IsAffineOpen V := hV
    refine ⟨Z.subschemeι ⁻¹ᵁ V, hxV, ?_⟩
    exact smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal Z hV' (c.restrict hVU) S
      (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S hS)
  choose W hyW hWsm using key
  have hsup : (⨆ y, W y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hyW y⟩
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top W hsup).mpr hWsm

/- English proof (authored)
At each point of the support, the strict normal crossing hypothesis provides a chart in which Z is a coordinate subspace. This is exactly the hypothesis of the local smoothness criterion for the closed subscheme.
-/
theorem smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth (Z.subschemeι ≫ p) := by
  unfold HasStrictNormalCrossingsWith at h
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal Z ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hS⟩ := h x hx
  exact ⟨U, hxU, n, c, S, hS⟩

/- English proof (authored)
Because r is a non-zero-divisor, multiplication by r is injective on R. Tensoring that injection with the flat R-algebra A gives an injective multiplication map on A. This map is multiplication by the image of r. By commutativity the image is a non-zero-divisor.
-/
private theorem algebraMap_mem_nonZeroDivisors_of_flat {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have hreg : IsSMulRegular A r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : A, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • (0 : A) := by
      rw [smul_zero, Algebra.smul_def]
      exact hx
    exact hreg hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

/- English proof (authored)
The relevant polynomial variable is nonzero in the polynomial ring over the field, which is a domain. It is therefore a non-zero-divisor. The chart algebra is étale and hence flat, so its image remains a non-zero-divisor. That image is the chart coordinate.
-/
theorem coord_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) : c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) := by
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    c.algebra_etale hU
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    inferInstance
  have halg : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      = c.coordRingHom := c.algebraMap_eq_coordRingHom
  have hXne : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hXnzd : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k)
      ∈ nonZeroDivisors (MvPolynomial (ULift.{u} (Fin m)) k) :=
    mem_nonZeroDivisors_of_ne_zero hXne
  have key : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      (MvPolynomial.X (ULift.up.{u} j)) ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) :=
    algebraMap_mem_nonZeroDivisors_of_flat hXnzd
  rw [halg] at key
  rwa [c.coordRingHom_X j] at key

/- English proof (authored)
Evaluate polynomials by setting the j-th variable to zero. The product of the s-th variable with r then evaluates to zero because it was a multiple of the j-th variable. The s-th variable is fixed by the evaluation and is nonzero in the polynomial domain. Thus r evaluates to zero. Passing to the quotient by the j-th variable is unchanged by the evaluation, as can be checked on constants and variables. It follows that r is zero in that quotient, so it belongs to the principal ideal.
-/
private theorem mem_span_X_of_X_mul_mem {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) (r : MvPolynomial σ k)
    (hr : MvPolynomial.X s * r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) :
    r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := by
  classical
  obtain ⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ k →+* MvPolynomial σ k,
      (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        ψ (MvPolynomial.X j) = 0 ∧
        ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by
    refine ⟨MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial σ k)
        (fun i : σ => if i = j then (0 : MvPolynomial σ k) else MvPolynomial.X i), ?_, ?_, ?_⟩
    · intro a
      simp
    · simp
    · intro i hi
      simp [hi]
  have hXjmem : (MvPolynomial.X j : MvPolynomial σ k)
      ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := Ideal.mem_span_singleton_self _
  have key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})).comp ψ
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      rw [RingHom.comp_apply]
      by_cases h : i = j
      · subst h
        rw [hψXj, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hXjmem).symm
      · rw [hψXi i h]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
  have h0 : ψ (MvPolynomial.X s * r) = 0 := by
    rw [ht, map_mul, hψXj, zero_mul]
  rw [map_mul, hψXi s (Ne.symm hjs)] at h0
  have hXs : (MvPolynomial.X s : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hXs
    · exact h
  have h3 := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

/- English proof (authored)
Choose polynomial representatives of a and b. The equality of the products says that the s-th variable times the difference of the representatives lies in the principal ideal of the j-th variable. The preceding divisibility result puts the difference itself in that ideal. Hence the two quotient classes agree.
-/
private theorem eq_of_mk_X_mul_eq_quotient_span_X {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s)
    (a b : MvPolynomial σ k ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (mem_span_X_of_X_mul_mem hjs (a' - b') h)

/- English proof (authored)
Form the quotient of A by the extension of I. The induced map from the quotient of P is a base change of f, so it is étale and in particular flat. Multiplication by the class of w is injective on the source quotient by hypothesis and stays injective after this flat base change. The given product is zero in the target quotient, so the class of x is zero there. This is membership in the extended ideal.
-/
private theorem mem_map_of_mul_mem_of_etale {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hreg : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := by
    intro a b h
    exact hw a b (by simpa only [smul_eq_mul] using h)
  have hregB : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg.of_flat
  have hy : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x
      = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I) := by
    rw [smul_zero]
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ((Ideal.Quotient.mk I) w) *
        (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hregB hy)

/- English proof (authored)
Extension along the chart map sends the ideal of the j-th variable to the ideal of the j-th coordinate and sends the s-th variable to the s-th coordinate. Multiplication by the s-th variable is injective in the polynomial quotient by the j-th variable because the indices differ. Apply the étale quotient argument to transfer this injectivity to the chart quotient. The product hypothesis now gives that the class of x in the chart quotient is zero.
-/
theorem mem_span_coord_of_coord_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    {j s : Fin m} (hjs : j ≠ s) (x : ↑(X.presheaf.obj (op U)))
    (hx : c.coord s * x ∈ Ideal.span {c.coord j}) : x ∈ Ideal.span {c.coord j} := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})
      = Ideal.span {c.coord j} := by
    rw [Ideal.map_span, Set.image_singleton, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => eq_of_mk_X_mul_eq_quotient_span_X hju a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x
      ∈ Ideal.map c.coordRingHom
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}) := by
    rw [hmapspan, c.coordRingHom_X]
    exact hx
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU)
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})
      (MvPolynomial.X (ULift.up s)) hu x hx'
  rw [hmapspan] at hfin
  exact hfin

/- English proof (authored)
Induct on the exponent n. Divisibility by the zeroth power is automatic. For the successor step, divisibility of the product by the higher power implies divisibility by the j-th variable. The distinct-variable result then shows that this variable divides r. Write r as that variable times a polynomial. Cancel one copy of the nonzero variable in the domain. The induction hypothesis says the remaining polynomial is divisible by the n-th power, which recovers the required higher power in r.
-/
private theorem X_pow_dvd_of_X_pow_dvd_X_mul {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) :
    ∀ (n : ℕ) (r : MvPolynomial σ k),
      (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r →
        (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ r := by
  intro n
  induction n with
  | zero =>
    intro r _
    rw [pow_zero]
    exact one_dvd r
  | succ n ih =>
    intro r hr
    have hXne : (MvPolynomial.X j : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
    have h1 : (MvPolynomial.X j : MvPolynomial σ k) ∣ MvPolynomial.X s * r :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hr
    have h2 : (MvPolynomial.X j : MvPolynomial σ k) ∣ r :=
      Ideal.mem_span_singleton.mp
        (mem_span_X_of_X_mul_mem hjs r (Ideal.mem_span_singleton.mpr h1))
    obtain ⟨r', rfl⟩ := h2
    have h3 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n ∣
        MvPolynomial.X j * (MvPolynomial.X s * r') := by
      have e1 : (MvPolynomial.X j : MvPolynomial σ k) * (MvPolynomial.X s * r')
          = MvPolynomial.X s * (MvPolynomial.X j * r') := by ring
      have e2 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n
          = MvPolynomial.X j ^ (n + 1) := by ring
      rw [e1, e2]
      exact hr
    have h4 : (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r' :=
      (mul_dvd_mul_iff_left hXne).mp h3
    have h5 := ih r' h4
    have e3 : (MvPolynomial.X j : MvPolynomial σ k) ^ (n + 1)
        = MvPolynomial.X j * MvPolynomial.X j ^ n := by ring
    rw [e3]
    exact mul_dvd_mul_left _ h5

/- English proof (authored)
Choose representatives in the polynomial ring. The product equality means the s-th variable times their difference is divisible by the n-th power of the j-th variable. The power divisibility result shows that the difference itself is divisible by this power, so the classes coincide.
-/
private theorem eq_of_mk_X_mul_eq_quotient_span_X_pow {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) (n : ℕ)
    (a b : MvPolynomial σ k ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
    (X_pow_dvd_of_X_pow_dvd_X_mul hjs n (a' - b') (Ideal.mem_span_singleton.mp h)))

/- English proof (authored)
The ideal of the variable power extends to the ideal of the same power of the chart coordinate. The polynomial quotient by that power has injective multiplication by the s-th variable by the preceding result for distinct indices. The étale map on the quotients is flat, so multiplication by the s-th chart coordinate is also injective on the chart quotient. The product hypothesis therefore forces x to vanish in that quotient.
-/
theorem mem_span_coord_pow_of_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    {j s : Fin m} (hjs : j ≠ s) (n : ℕ) (x : ↑(X.presheaf.obj (op U)))
    (hx : c.coord s * x ∈ Ideal.span {c.coord j ^ n}) :
    x ∈ Ideal.span {c.coord j ^ n} := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      = Ideal.span {c.coord j ^ n} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_pow hju n a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x
      ∈ Ideal.map c.coordRingHom
          (Ideal.span
            {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}) := by
    rw [hmapspan, c.coordRingHom_X]
    exact hx
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU)
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      (MvPolynomial.X (ULift.up s)) hu x hx'
  rw [hmapspan] at hfin
  exact hfin

/- English proof (authored)
The inclusion of V identifies a section on V with a global section of the open subscheme V. The map on sections is the inverse of the canonical identification from global sections back to sections on V.
-/
private theorem appLE_ι_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ hle = V.topIso.inv := by
  simp
  rfl

/- English proof (authored)
The indicated section map is the inverse of the canonical ring isomorphism. It is therefore bijective.
-/
private theorem bijective_appLE_ι_top {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) := by
  rw [appLE_ι_top_eq_topIso_inv V hle]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective

/- English proof (authored)
The ideal of the restricted sheaf on the affine scheme V is the extension of the original section ideal along the canonical section-ring isomorphism. By hypothesis the extension is the whole ring. Contracting it back along the isomorphism gives the whole original ring, which is the asserted section ideal.
-/
private theorem ideal_eq_top_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := V.ι_preimage_self.ge
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ hle
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩) = ⊤ :=
    key.symm
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩))
      = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact bijective_appLE_ι_top V hle
  rw [← hcomap, key2, Ideal.comap_top]

/- English proof (authored)
At x, choose the chart supplied by the hypothesis and shrink it to an affine neighbourhood. If D restricts to the unit ideal, its section ideal is generated by 1. Otherwise the restricted chart identifies its section ideal with the principal ideal of the chosen coordinate. That coordinate is a non-zero-divisor. In both cases this gives the required affine neighbourhood and generator.
-/
theorem isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor D := by
  intro x
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨f, hf, hfspan⟩ :
      ∃ f : ↑(X.presheaf.obj (op V)), f ∈ nonZeroDivisors ↑(X.presheaf.obj (op V)) ∧
        D.ideal ⟨V, hV⟩ = Ideal.span {f} := by
    rcases hc with htop | ⟨j, hj⟩
    · refine ⟨1, one_mem _, ?_⟩
      rw [ideal_eq_top_of_restrictIdeal_eq_top D hV (restrictIdeal_eq_top_of_le D hVU htop),
        Ideal.span_singleton_one]
    · refine ⟨(c.restrict hVU).coord j, coord_mem_nonZeroDivisors hV (c.restrict hVU) j, ?_⟩
      rw [(c.restrict hVU).ideal_eq_span_coord hV D {j}
        (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hj), Finset.coe_singleton,
        Set.image_singleton]
  exact ⟨⟨V, hV⟩, f, hxV, hf, hfspan⟩

/- English proof (authored)
The support of the restriction is the inverse image of the original support. By hypothesis the restriction is the unit ideal, which has empty support. Therefore x, a point of U, is outside the original support.
-/
private theorem notMem_support_of_mem_of_restrictIdeal_eq_top {Y : Scheme.{u}}
    (I : Y.IdealSheafData) {U : Y.Opens} (h : restrictIdeal I U = ⊤) {x : Y} (hxU : x ∈ U) :
    x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

/- English proof (authored)
The local chart descriptions give a non-zero-divisor generator at each point by the preceding criterion. At a point of the support, the unit-ideal alternative cannot occur because the unit ideal has empty support on the chart. Thus at such a point the ideal is a coordinate hyperplane ideal. The smoothness result for closed subschemes that are locally coordinate subspaces applies, proving the second condition for a smooth divisor.
-/
theorem isSmoothDivisor_of_locally_coordIdeal (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    IsSmoothDivisor p D := by
  rw [isSmoothDivisor_iff]
  refine ⟨isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal D h, smooth_subschemeι_comp_of_locally_eq_coordIdeal D ?_⟩
  intro x hx
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  rcases hc with hc | ⟨j, hj⟩
  · exact absurd hx (notMem_support_of_mem_of_restrictIdeal_eq_top D hc hxU)
  · exact ⟨U, hxU, n, c, {j}, hj⟩

end FunctorialResolution.EmbeddedResolution
