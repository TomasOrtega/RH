import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*} [TopologicalSpace α]

/- English proof (authored)
The kernel is contained in its radical. If an element has a power in the kernel, its image has a power equal to zero. The target ring is reduced, so the image is zero and the original element already lies in the kernel.
-/
private theorem radical_ringHom_ker_eq {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [RingHom.mem_ker] at hn ⊢
  have hx : φ x ^ n = 0 := by rw [← map_pow]; exact hn
  exact IsNilpotent.eq_zero ⟨n, hx⟩

/- English proof (authored)
A Noetherian space has finitely many irreducible components, each closed. The selected family is a subset of this finite family, so its union is closed.
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

/- English proof (authored)
The excluded components are a family of irreducible components of the Noetherian space. Their union is closed, so its complement is open.
-/
theorem isOpen_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    (S : Set (Set α)) :
    IsOpen ((⋃₀ (irreducibleComponents α \ S))ᶜ) :=
  (isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl

/- English proof (authored)
Every point lies on an irreducible component. If the point avoids the union of excluded components, any such component through the point must belong to the selected family. Hence the point belongs to that family's union.
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

/- English proof (authored)
The open complement of the excluded components lies in the selected union, which is closed, so its closure also lies there. Conversely take a selected component. It cannot be contained in the union of excluded components, because that is a finite union of closed sets and irreducibility would put it inside a single excluded component. Maximality would then identify the two components, contradicting the choice. Thus the selected component meets the complement in a nonempty open subset, which is dense in that component. Every selected component therefore lies in the closure.
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

/- English proof (authored)
Closed subsets with the same underlying set are equal. Their vanishing ideal sheaves are therefore equal.
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
/- English proof (authored)
The open is defined as the complement of the union of the excluded irreducible components, so its underlying subset is exactly that complement.
-/
theorem coe_complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl

/- English proof (authored)
The kernel ideal sheaf is contained in its radical. For the reverse containment, on each affine target open the ideal of the kernel sheaf lies in the kernel of the section map. Sections over the inverse image form a reduced ring because the source scheme is reduced. The kernel of this section map is therefore radical and also contains the radical of the kernel sheaf ideal on that open. These local containments give containment in the kernel ideal sheaf, which is determined by the section kernels.
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

/- English proof (authored)
The ideal of the support of an ideal sheaf is its radical. Here the kernel sheaf equals its radical because the source is reduced, and its support is the given closed subset. Thus its kernel is the vanishing ideal of that subset.
-/
private theorem ker_eq_vanishingIdeal_of_support {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] {Z : Closeds ↥Y}
    (hZ : ((Scheme.Hom.ker g).support : Set ↥Y) = (Z : Set ↥Y)) :
    Scheme.Hom.ker g = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_scheme_ker_eq g]

/- English proof (authored)
Let the open in the target be the complement of the excluded irreducible components. Its closure is the selected union, so the support of the kernel of the open inclusion is that union. Since the open is reduced, the kernel is its support's vanishing ideal.

The closure of the inverse image of the open is contained in the inverse image of the selected union because the latter is closed. For the reverse inclusion, take any point above a selected component. Its image is a specialization of that component's generic point. The generic point belongs to the open, because any excluded component containing it would contain the selected component and hence equal it. Flatness lifts this generalization of the image to a generalization of the original point. That lift belongs to the inverse image of the open, so the original point is in its closure. The preimage open inclusion therefore has kernel the vanishing ideal of the inverse image of the selected union. Both open inclusions are quasi-compact by Noetherianity. The flat pullback formula for the kernels of their pullback square gives the desired equality.
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
