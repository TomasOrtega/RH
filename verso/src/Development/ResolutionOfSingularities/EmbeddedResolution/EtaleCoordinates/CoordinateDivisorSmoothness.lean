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

/- English proof (translation)
Establish `i3 : HasRingHomProperty (@Smooth.{u}) (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth)` using `inferInstance`. Establish `hloc : IsZariskiLocalAtSource (@Smooth.{u})` using `@HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3`. Establish `hVtop : (⨆ i : PLift ι, U i.down) = ⊤`. Rewrite using `[← hU]`. Conclude with `le_antisymm (iSup_le fun i => le_iSup U i.down) (iSup_le fun i => le_iSup (fun j : PLift ι => U j.down) (PLift.up i))`.

Conclude with `(IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun i : PLift ι => U i.down) hVtop).mpr fun i => h i.down`.
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

/- English proof (translation)
Establish `h' : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map`. Rewrite using `[← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]`. Rewrite using `[restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map, Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`.
-/
theorem restrictIdeal_eq_restrict_coordIdeal_of_le {U V : X.Opens} (hVU : V ≤ U) (c : EtaleChart p U m)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal Z V = (c.restrict hVU).coordIdeal S := by
  have h' : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]

/- English proof (translation)
Rewrite using `[restrictIdeal_eq_comap_homOfLE_restrictIdeal Z hVU, h, Scheme.IdealSheafData.comap_top]`.
-/
theorem restrictIdeal_eq_top_of_le {Y : Scheme.{u}} (Z : Y.IdealSheafData) {U V : Y.Opens}
    (hVU : V ≤ U) (h : restrictIdeal Z U = ⊤) : restrictIdeal Z V = ⊤ := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal Z hVU, h, Scheme.IdealSheafData.comap_top]

/- English proof (translation)
Establish `hsm : Smooth (affineSpaceFinToSpec k (m - S.card))` using `affineSpaceIsSmooth ..`. Establish `het : Etale (c.restrictToSubscheme hU Z S h).map` using `(c.restrictToSubscheme hU Z S h).isEtale`. Establish `hsm2 : Smooth (c.restrictToSubscheme hU Z S h).map` using `inferInstance`. Establish `hc : (c.restrictToSubscheme hU Z S h).map ≫ affineSpaceFinToSpec k (m - S.card) = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)` using `(c.restrictToSubscheme hU Z S h).comp_struct`. Rewrite using `[← hc]`.

Use `infer_instance`.
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

/- English proof (translation)
Establish `i3 : HasRingHomProperty (@Smooth.{u}) (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth)` using `inferInstance`. Establish `hloc : IsZariskiLocalAtSource (@Smooth.{u})` using `@HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3`. Establish `key : ∀ y : ↥Z.subscheme, ∃ W : (Z.subscheme).Opens, y ∈ W ∧ Smooth (W.ι ≫ (Z.subschemeι ≫ p))`. Introduce `y`. Establish `hy : Z.subschemeι.base y ∈ Z.support`.

Establish `hmem : Z.subschemeι.base y ∈ Set.range Z.subschemeι.base` using `Set.mem_range_self y`. Simplify using `using hmem`. Take `⟨U, hxU, n, c, S, hS⟩` from `h _ hy`. Take `⟨V, hV, hxV, hVU⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU`. Establish `hV' : IsAffineOpen V` using `hV`.

Use `⟨Z.subschemeι ⁻¹ᵁ V, hxV, ?_⟩` and prove the remaining obligations. Conclude with `smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal Z hV' (c.restrict hVU) S (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S hS)`. Use `choose W hyW hWsm using key`. Establish `hsup : (⨆ y, W y) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Conclude with `Opens.mem_iSup.mpr ⟨y, hyW y⟩`. Conclude with `(IsZariskiLocalAtSource.iff_of_iSup_eq_top W hsup).mpr hWsm`.
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

/- English proof (translation)
Unfold `HasStrictNormalCrossingsWith at h`. Use `smooth_subschemeι_comp_of_locally_eq_coordIdeal Z ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨U, hxU, n, c, a, S, -, -, -, hS⟩` from `h x hx`. Conclude with `⟨U, hxU, n, c, S, hS⟩`.
-/
theorem smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth (Z.subschemeι ≫ p) := by
  unfold HasStrictNormalCrossingsWith at h
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal Z ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hS⟩ := h x hx
  exact ⟨U, hxU, n, c, S, hS⟩

/- English proof (translation)
Establish `hreg : IsSMulRegular A r` using `Module.Flat.isSMulRegular_of_nonZeroDivisors hr`. Establish `key : ∀ x : A, algebraMap R A r * x = 0 → x = 0`. Introduce `x hx`. Establish `hsm : r • x = r • (0 : A)`. Rewrite using `[smul_zero, Algebra.smul_def]`.

Conclude with `hx`. Conclude with `hreg hsm`. Rewrite using `[mem_nonZeroDivisors_iff]`. Conclude with `⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩`.
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

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U))` to `c.algebra`. Establish `: Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U))` using `c.algebra_etale hU`. Establish `: Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U))` using `inferInstance`. Establish `halg : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U))) = c.coordRingHom` using `c.algebraMap_eq_coordRingHom`. Establish `hXne : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0` using `MvPolynomial.X_ne_zero _`.

Establish `hXnzd : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k) ∈ nonZeroDivisors (MvPolynomial (ULift.{u} (Fin m)) k)` using `mem_nonZeroDivisors_of_ne_zero hXne`. Establish `key : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U))) (MvPolynomial.X (ULift.up.{u} j)) ∈ nonZeroDivisors ↑(X.presheaf.obj (op U))` using `algebraMap_mem_nonZeroDivisors_of_flat hXnzd`. Rewrite `key` using `[halg]`. Rewrite `key` using `[c.coordRingHom_X j]`. Then use the resulting hypothesis.
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

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ k →+* MvPolynomial σ k, (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧ ψ (MvPolynomial.X j) = 0 ∧ ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by`. Use `⟨MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial σ k) (fun i : σ => if i = j then (0 : MvPolynomial σ k) else MvPolynomial.X i), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce `i hi`. Simplify using `[hi]`. Establish `hXjmem : (MvPolynomial.X j : MvPolynomial σ k) ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}` using `Ideal.mem_span_singleton_self _`. Establish `key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})).comp ψ = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Rewrite using `[RingHom.comp_apply, hψC]`. Introduce `i`. Rewrite using `[RingHom.comp_apply]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[hψXj, map_zero]`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem.mpr hXjmem).symm`. Rewrite using `[hψXi i h]`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton.mp hr`.

Establish `h0 : ψ (MvPolynomial.X s * r) = 0`. Rewrite using `[ht, map_mul, hψXj, zero_mul]`. Rewrite `h0` using `[map_mul, hψXi s (Ne.symm hjs)]`. Establish `hXs : (MvPolynomial.X s : MvPolynomial σ k) ≠ 0` using `MvPolynomial.X_ne_zero _`. Establish `hψr : ψ r = 0`.

Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd h hXs`. Conclude with `h`. Establish `h3` using `DFunLike.congr_fun key r`. Rewrite `h3` using `[RingHom.comp_apply, hψr, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h3.symm`.
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

/- English proof (translation)
Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `h` using `[← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]`. Conclude with `Ideal.Quotient.eq.mpr (mem_span_X_of_X_mul_mem hjs (a' - b') h)`.
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

/- English proof (translation)
Establish `hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale` using `etale_quotientMap hf I`. Set `_ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I)` to `(Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra`. Establish `: Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I)` using `hg`. Establish `: Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I)` using `inferInstance`. Establish `hreg : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w)`.

Introduce `a b h`. Conclude with `hw a b (by simpa only [smul_eq_mul] using h)`. Establish `hregB : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w)` using `hreg.of_flat`. Establish `hy : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I)`. Rewrite using `[smul_zero]`.

Use `show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0`. Rewrite using `[Ideal.quotientMap_mk, ← map_mul]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hx`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp (hregB hy)`.
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

/- English proof (translation)
Establish `hmapspan : Ideal.map c.coordRingHom (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}) = Ideal.span {c.coord j}`. Rewrite using `[Ideal.map_span, Set.image_singleton, c.coordRingHom_X]`. Establish `hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s`. Introduce `h`. Conclude with `hjs (congrArg ULift.down h)`.

Establish `hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸ Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}, (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})) (MvPolynomial.X (ULift.up s)) * a = (Ideal.Quot …` using `fun a b h => eq_of_mk_X_mul_eq_quotient_span_X hju a b h`. Establish `hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x ∈ Ideal.map c.coordRingHom (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)})`. Rewrite using `[hmapspan, c.coordRingHom_X]`. Conclude with `hx`. Establish `hfin` using `mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU) (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k)}) (MvPolynomial.X (ULift.up s)) hu x hx'`.

Rewrite `hfin` using `[hmapspan]`. Conclude with `hfin`.
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

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `r _`. Rewrite using `[pow_zero]`.

Conclude with `one_dvd r`. Consider the case `succ n ih`. Introduce `r hr`. Establish `hXne : (MvPolynomial.X j : MvPolynomial σ k) ≠ 0` using `MvPolynomial.X_ne_zero _`. Establish `h1 : (MvPolynomial.X j : MvPolynomial σ k) ∣ MvPolynomial.X s * r` using `dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hr`.

Establish `h2 : (MvPolynomial.X j : MvPolynomial σ k) ∣ r` using `Ideal.mem_span_singleton.mp (mem_span_X_of_X_mul_mem hjs r (Ideal.mem_span_singleton.mpr h1))`. Take `⟨r', rfl⟩` from `h2`. Establish `h3 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n ∣ MvPolynomial.X j * (MvPolynomial.X s * r')`. Establish `e1 : (MvPolynomial.X j : MvPolynomial σ k) * (MvPolynomial.X s * r') = MvPolynomial.X s * (MvPolynomial.X j * r')` using `by ring`. Establish `e2 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n = MvPolynomial.X j ^ (n + 1)` using `by ring`.

Rewrite using `[e1, e2]`. Conclude with `hr`. Establish `h4 : (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r'` using `(mul_dvd_mul_iff_left hXne).mp h3`. Establish `h5` using `ih r' h4`. Establish `e3 : (MvPolynomial.X j : MvPolynomial σ k) ^ (n + 1) = MvPolynomial.X j * MvPolynomial.X j ^ n` using `by ring`.

Rewrite using `[e3]`. Conclude with `mul_dvd_mul_left _ h5`.
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

/- English proof (translation)
Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `h` using `[← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]`. Conclude with `Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (X_pow_dvd_of_X_pow_dvd_X_mul hjs n (a' - b') (Ideal.mem_span_singleton.mp h)))`.
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

/- English proof (translation)
Establish `hmapspan : Ideal.map c.coordRingHom (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}) = Ideal.span {c.coord j ^ n}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_pow, c.coordRingHom_X]`. Establish `hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s`. Introduce `h`. Conclude with `hjs (congrArg ULift.down h)`.

Establish `hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸ Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}, (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})) (MvPolynomial.X (ULift.up s)) * a = (Id …` using `fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_pow hju n a b h`. Establish `hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x ∈ Ideal.map c.coordRingHom (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})`. Rewrite using `[hmapspan, c.coordRingHom_X]`. Conclude with `hx`. Establish `hfin` using `mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU) (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}) (MvPolynomial.X (ULift.up s)) hu x hx'`.

Rewrite `hfin` using `[hmapspan]`. Conclude with `hfin`.
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

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem appLE_ι_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ hle = V.topIso.inv := by
  simp
  rfl

/- English proof (translation)
Rewrite using `[appLE_ι_top_eq_topIso_inv V hle]`. Conclude with `V.topIso.commRingCatIsoToRingEquiv.symm.bijective`.
-/
private theorem bijective_appLE_ι_top {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) := by
  rw [appLE_ι_top_eq_topIso_inv V hle]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V` using `V.ι_preimage_self.ge`. Establish `key` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ hle`. Rewrite `key` using `[← restrictIdeal_eq_comap_ι, htop]`. Establish `h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤`.

Simplify using the standard rewrite rules. Rewrite `key` using `[h0]`. Establish `key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩) = ⊤` using `key.symm`. Establish `hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩`. Apply `Ideal.comap_map_of_bijective` to reduce the goal to its premises.

Conclude with `bijective_appLE_ι_top V hle`. Rewrite using `[← hcomap, key2, Ideal.comap_top]`.
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

/- English proof (translation)
Introduce `x`. Take `⟨U, hxU, n, c, hc⟩` from `h x`. Take `⟨V, hV, hxV, hVU⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf, hfspan⟩ : ∃ f : ↑(X.presheaf.obj (op V)), f ∈ nonZeroDivisors ↑(X.presheaf.obj (op V)) ∧ D.ideal ⟨V, hV⟩ = Ideal.span {f} := by`. Break down `hc with htop | ⟨j, hj⟩` into its components or cases.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[ideal_eq_top_of_restrictIdeal_eq_top D hV (restrictIdeal_eq_top_of_le D hVU htop), Ideal.span_singleton_one]`. Use `⟨(c.restrict hVU).coord j, coord_mem_nonZeroDivisors hV (c.restrict hVU) j, ?_⟩` and prove the remaining obligations. Rewrite using `[(c.restrict hVU).ideal_eq_span_coord hV D {j} (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hj), Finset.coe_singleton, Set.image_singleton]`. Conclude with `⟨⟨V, hV⟩, f, hxV, hf, hfspan⟩`.
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

/- English proof (translation)
Introduce `hx`. Establish `h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support`. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`. Conclude with `hx`. Rewrite `h1` using `[← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top]`.

Establish `h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U)` using `h1`. Simplify using `at h2`.
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

/- English proof (translation)
Rewrite using `[isSmoothDivisor_iff]`. Use `⟨isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal D h, smooth_subschemeι_comp_of_locally_eq_coordIdeal D ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨U, hxU, n, c, hc⟩` from `h x`. Break down `hc with hc | ⟨j, hj⟩` into its components or cases.

Conclude with `absurd hx (notMem_support_of_mem_of_restrictIdeal_eq_top D hc hxU)`. Conclude with `⟨U, hxU, n, c, {j}, hj⟩`.
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
