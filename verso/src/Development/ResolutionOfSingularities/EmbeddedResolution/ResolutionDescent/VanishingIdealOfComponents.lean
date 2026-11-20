import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*} [TopologicalSpace α]

/- English proof (translation)
Use `le_antisymm ?_ Ideal.le_radical` and prove the remaining obligations. Introduce and unpack `x ⟨n, hn⟩`. Rewrite `hn`, the goal using `[RingHom.mem_ker]`. Establish `hx : φ x ^ n = 0` using `by rw [← map_pow]; exact hn`. Conclude with `IsNilpotent.eq_zero ⟨n, hx⟩`.
-/
private theorem radical_ringHom_ker_eq {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [RingHom.mem_ker] at hn ⊢
  have hx : φ x ^ n = 0 := by rw [← map_pow]; exact hn
  exact IsNilpotent.eq_zero ⟨n, hx⟩

/- English proof (translation)
Establish `hfin : S.Finite` using `Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) hS`. Rewrite using `[Set.sUnion_eq_biUnion]`. Use `hfin.isClosed_biUnion ?_` and prove the remaining obligations. Introduce `s hs`. Apply `isClosed_of_mem_irreducibleComponents` to reduce the goal to its premises.

Conclude with `hS hs`.
-/
theorem isClosed_sUnion_irreducibleComponents [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    IsClosed (⋃₀ S) := by
  have hfin : S.Finite :=
    Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) hS
  rw [Set.sUnion_eq_biUnion]
  refine hfin.isClosed_biUnion ?_
  intro s hs
  apply isClosed_of_mem_irreducibleComponents
  exact hS hs

/- English proof (translation)
The claim follows from `(isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl`.
-/
theorem isOpen_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    (S : Set (Set α)) :
    IsOpen ((⋃₀ (irreducibleComponents α \ S))ᶜ) :=
  (isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[Set.mem_compl_iff]`. Establish `hmem : x ∈ irreducibleComponent x` using `by apply mem_irreducibleComponent`. Establish `hcomp : irreducibleComponent x ∈ irreducibleComponents α`. Apply `irreducibleComponent_mem_irreducibleComponents` to reduce the goal to its premises.

Distinguish the cases in `hC : irreducibleComponent x ∈ S`. Conclude with `⟨irreducibleComponent x, hC, hmem⟩`. Conclude with `(hx ⟨irreducibleComponent x, ⟨hcomp, hC⟩, hmem⟩).elim`.
-/
theorem compl_sUnion_irreducibleComponents_sdiff_subset (S : Set (Set α)) :
    (⋃₀ (irreducibleComponents α \ S))ᶜ ⊆ ⋃₀ S := by
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hmem : x ∈ irreducibleComponent x := by apply mem_irreducibleComponent
  have hcomp : irreducibleComponent x ∈ irreducibleComponents α := by
    apply irreducibleComponent_mem_irreducibleComponents
  by_cases hC : irreducibleComponent x ∈ S
  · exact ⟨irreducibleComponent x, hC, hmem⟩
  · exact (hx ⟨irreducibleComponent x, ⟨hcomp, hC⟩, hmem⟩).elim

/- English proof (translation)
Establish `hZcl : IsClosed (⋃₀ (irreducibleComponents α \ S))` using `isClosed_sUnion_irreducibleComponents Set.sdiff_subset`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Conclude with `closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S) (isClosed_sUnion_irreducibleComponents hS)`. Introduce and unpack `x ⟨C, hCS, hxC⟩`. Establish `hCcomp : C ∈ irreducibleComponents α` using `hS hCS`.

Establish `hCirr : IsIrreducible C` using `hCcomp.1`. Establish `hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents α \ S)`. Introduce `hsub`. Establish `hfin : (irreducibleComponents α \ S).Finite` using `Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) Set.sdiff_subset`. Take `⟨D, hD, hCsubD⟩` from `isIrreducible_iff_sUnion_isClosed.mp hCirr hfin.toFinset (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1) (by rwa [hfin.coe_toFinset])`.

Establish `hD' : D ∈ irreducibleComponents α \ S` using `hfin.mem_toFinset.mp hD`. Establish `hDsubC : D ⊆ C` using `hCcomp.2 hD'.1.1 hCsubD`. Conclude with `hD'.2 (by rw [Set.Subset.antisymm hDsubC hCsubD]; exact hCS)`. Take `⟨y, hyC, hyZ⟩` from `Set.not_subset.mp hnot`. Rewrite using `[mem_closure_iff]`.

Introduce `o ho hxo`. Take `⟨z, hz, hzo, hzZ⟩` from `hCirr.2 o (⋃₀ (irreducibleComponents α \ S))ᶜ ho hZcl.isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩`. Conclude with `⟨z, hzo, hzZ⟩`.
-/
theorem closure_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    closure ((⋃₀ (irreducibleComponents α \ S))ᶜ) = ⋃₀ S := by
  have hZcl : IsClosed (⋃₀ (irreducibleComponents α \ S)) :=
    isClosed_sUnion_irreducibleComponents Set.sdiff_subset
  apply Set.Subset.antisymm
  · exact closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S)
      (isClosed_sUnion_irreducibleComponents hS)
  · rintro x ⟨C, hCS, hxC⟩
    have hCcomp : C ∈ irreducibleComponents α := hS hCS
    have hCirr : IsIrreducible C := hCcomp.1
    have hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents α \ S) := by
      intro hsub
      have hfin : (irreducibleComponents α \ S).Finite :=
        Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents)
          Set.sdiff_subset
      obtain ⟨D, hD, hCsubD⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin.toFinset
        (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1)
        (by rwa [hfin.coe_toFinset])
      have hD' : D ∈ irreducibleComponents α \ S := hfin.mem_toFinset.mp hD
      have hDsubC : D ⊆ C := hCcomp.2 hD'.1.1 hCsubD
      exact hD'.2 (by rw [Set.Subset.antisymm hDsubC hCsubD]; exact hCS)
    obtain ⟨y, hyC, hyZ⟩ := Set.not_subset.mp hnot
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, hz, hzo, hzZ⟩ := hCirr.2 o (⋃₀ (irreducibleComponents α \ S))ᶜ ho
      hZcl.isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩
    exact ⟨z, hzo, hzZ⟩

/- English proof (translation)
Establish `hZ : Z₁ = Z₂` using `SetLike.coe_injective h`. Rewrite using `[hZ]`.
-/
theorem vanishingIdeal_congr {X : Scheme.{u}} {Z₁ Z₂ : Closeds ↥X}
    (h : (Z₁ : Set ↥X) = (Z₂ : Set ↥X)) :
    Scheme.IdealSheafData.vanishingIdeal Z₁ = Scheme.IdealSheafData.vanishingIdeal Z₂ := by
  have hZ : Z₁ = Z₂ := SetLike.coe_injective h
  rw [hZ]

def complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents ↥X \ S))ᶜ,
    isOpen_compl_sUnion_irreducibleComponents_sdiff S⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl

/- English proof (translation)
Use `le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)` and prove the remaining obligations. Use `show (Scheme.Hom.ker g).radical ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (CommRingCat.Hom.hom (g.app U.1))`. Use `Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_` and prove the remaining obligations. Introduce `U`. Use `AlgebraicGeometry.IsReduced.component_reduced (X := X) (g ⁻¹ᵁ U.1)` as an intermediate fact.

Establish `hle : (Scheme.Hom.ker g).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (g.app U.1))`. Unfold `AlgebraicGeometry.Scheme.Hom.ker`. Conclude with `Scheme.IdealSheafData.ideal_ofIdeals_le _ U`. Rewrite using `[Scheme.IdealSheafData.radical_ideal]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem radical_scheme_ker_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  show (Scheme.Hom.ker g).radical ≤
    Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (CommRingCat.Hom.hom (g.app U.1))
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U
  have := AlgebraicGeometry.IsReduced.component_reduced (X := X) (g ⁻¹ᵁ U.1)
  have hle : (Scheme.Hom.ker g).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
    unfold AlgebraicGeometry.Scheme.Hom.ker
    exact Scheme.IdealSheafData.ideal_ofIdeals_le _ U
  rw [Scheme.IdealSheafData.radical_ideal]
  calc ((Scheme.Hom.ker g).ideal U).radical
      ≤ (RingHom.ker (CommRingCat.Hom.hom (g.app U.1))).radical := Ideal.radical_mono hle
    _ = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := radical_ringHom_ker_eq _

/- English proof (translation)
Rewrite using `[← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support, radical_scheme_ker_eq g]`.
-/
private theorem ker_eq_vanishingIdeal_of_support {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] {Z : Closeds ↥Y}
    (hZ : ((Scheme.Hom.ker g).support : Set ↥Y) = (Z : Set ↥Y)) :
    Scheme.Hom.ker g = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_scheme_ker_eq g]

/- English proof (translation)
Establish `hq1 : QuasiCompact (complSUnionOtherComponents X S).ι` using `⟨fun _ _ _ => NoetherianSpace.isCompact _⟩`. Establish `hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).ι` using `⟨fun _ _ _ => NoetherianSpace.isCompact _⟩`. Establish `hclU : closure ((complSUnionOtherComponents X S : X.Opens) : Set ↥X) = (Z : Set ↥X)`. Rewrite using `[coe_complSUnionOtherComponents, hZ]`. Conclude with `closure_compl_sUnion_irreducibleComponents_sdiff hS`.

Establish `h1 : (complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z`. Apply `ker_eq_vanishingIdeal_of_support` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.support_ker, ← hclU]`. Use `congr 1`. Conclude with `Scheme.Opens.range_ι _`.

Establish `hclU' : closure ((f ⁻¹ᵁ complSUnionOtherComponents X S : X'.Opens) : Set ↥X') = (Z' : Set ↥X')`. Establish `hcl : IsClosed (⇑f.base ⁻¹' (⋃₀ S))`. Rewrite using `[← hZ']`. Conclude with `Z'.2`. Rewrite using `[hZ']`.

Use `show closure (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)) = ⇑f.base ⁻¹' (⋃₀ S)`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Conclude with `closure_minimal (Set.preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl`. Introduce `x' hx'`. Establish `hx'' : f.base x' ∈ ⋃₀ S` using `hx'`.

Take `⟨C, hCS, hfx⟩` from `hx''`. Establish `hCcomp : C ∈ irreducibleComponents ↥X` using `hS hCS`. Take `⟨η, hη⟩` from `QuasiSober.sober hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)`. Establish `hηU : η ∈ (⋃₀ (irreducibleComponents ↥X \ S))ᶜ`. Introduce and unpack `⟨D, ⟨hDcomp, hDS⟩, hηD⟩`.

Establish `hCsubD : C ⊆ D`. Rewrite using `[← hη]`. Conclude with `(isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηD)`. Establish `hDsubC : D ⊆ C` using `hCcomp.2 hDcomp.1 hCsubD`. Conclude with `hDS (Set.Subset.antisymm hCsubD hDsubC ▸ hCS)`.

Establish `hspec : η ⤳ f.base x'`. Rewrite using `[specializes_iff_mem_closure, hη]`. Conclude with `hfx`. Take `⟨y', hy'spec, hy'eq⟩` from `AlgebraicGeometry.Flat.generalizingMap f hspec`. Establish `hy'mem : f.base y' ∈ ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)`.

Rewrite using `[hy'eq]`. Conclude with `hηU`. Establish `hy'mem2 : y' ∈ (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ))` using `hy'mem`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr hy'mem2) (specializes_iff_mem_closure.mp hy'spec)`. Establish `h2 : (f ⁻¹ᵁ complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z'`.

Apply `ker_eq_vanishingIdeal_of_support` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.support_ker, ← hclU']`. Use `congr 1`. Conclude with `Scheme.Opens.range_ι _`. Establish `hpb` using `isPullback_morphismRestrict f (complSUnionOtherComponents X S)`.

Establish `h4` using `ker_eq_comap_ker_of_isPullback_of_flat hpb`. Rewrite using `[← h1, ← h2, h4]`.
-/
theorem comap_vanishingIdeal_sUnion {X X' : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [AlgebraicGeometry.Flat f]
    {S : Set (Set ↥X)} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' := by
  have hq1 : QuasiCompact (complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hclU : closure ((complSUnionOtherComponents X S : X.Opens) : Set ↥X) = (Z : Set ↥X) := by
    rw [coe_complSUnionOtherComponents, hZ]
    exact closure_compl_sUnion_irreducibleComponents_sdiff hS
  have h1 : (complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU]
    congr 1
    exact Scheme.Opens.range_ι _
  have hclU' :
      closure ((f ⁻¹ᵁ complSUnionOtherComponents X S : X'.Opens) : Set ↥X') = (Z' : Set ↥X') := by
    have hcl : IsClosed (⇑f.base ⁻¹' (⋃₀ S)) := by
      rw [← hZ']; exact Z'.2
    rw [hZ']
    show closure (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ))
        = ⇑f.base ⁻¹' (⋃₀ S)
    apply Set.Subset.antisymm
    · exact closure_minimal
        (Set.preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl
    · intro x' hx'
      have hx'' : f.base x' ∈ ⋃₀ S := hx'
      obtain ⟨C, hCS, hfx⟩ := hx''
      have hCcomp : C ∈ irreducibleComponents ↥X := hS hCS
      obtain ⟨η, hη⟩ :=
        QuasiSober.sober hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)
      have hηU : η ∈ (⋃₀ (irreducibleComponents ↥X \ S))ᶜ := by
        rintro ⟨D, ⟨hDcomp, hDS⟩, hηD⟩
        have hCsubD : C ⊆ D := by
          rw [← hη]
          exact (isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hηD)
        have hDsubC : D ⊆ C := hCcomp.2 hDcomp.1 hCsubD
        exact hDS (Set.Subset.antisymm hCsubD hDsubC ▸ hCS)
      have hspec : η ⤳ f.base x' := by
        rw [specializes_iff_mem_closure, hη]
        exact hfx
      obtain ⟨y', hy'spec, hy'eq⟩ := AlgebraicGeometry.Flat.generalizingMap f hspec
      have hy'mem : f.base y' ∈ ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ) := by
        rw [hy'eq]; exact hηU
      have hy'mem2 : y' ∈ (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)) := hy'mem
      exact closure_mono (Set.singleton_subset_iff.mpr hy'mem2)
        (specializes_iff_mem_closure.mp hy'spec)
  have h2 : (f ⁻¹ᵁ complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z' := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU']
    congr 1
    exact Scheme.Opens.range_ι _
  have hpb := isPullback_morphismRestrict f (complSUnionOtherComponents X S)
  have h4 := ker_eq_comap_ker_of_isPullback_of_flat hpb
  rw [← h1, ← h2, h4]

end FunctorialResolution.EmbeddedResolution
