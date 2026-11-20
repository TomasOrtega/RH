import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsSmoothDivisorStableUnderSmoothPullback : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P Y : Scheme.{u})
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (g : Y ⟶ P) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)]
    (D : P.IdealSheafData), IsSmoothDivisor p D → IsSmoothDivisor (g ≫ p) (D.comap g)

/- English proof (authored)
Restriction is pullback along the open inclusion. Thus each side is pullback along one of the two composites in the commuting square, and those composites agree.
-/
private theorem restrictIdeal_comap_eq_comap_restrictIdeal {P Y : Scheme.{u}} (g : Y ⟶ P)
    (I : P.IdealSheafData) {U : P.Opens} {V : Y.Opens} {f : V.toScheme ⟶ U.toScheme}
    (hf : f ≫ U.ι = V.ι ≫ g) :
    restrictIdeal (I.comap g) V = (restrictIdeal I U).comap f := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hf]

/- English proof (authored)
The source open lies in the inverse image of the target open, so the morphism restricts to a map between them. The restriction identity expresses both ideals as pullbacks along that map. Pullback preserves the given inclusion.
-/
private theorem restrictIdeal_comap_le_of_restrictIdeal_le {P Y : Scheme.{u}} (g : Y ⟶ P)
    {I J : P.IdealSheafData} {U : P.Opens}
    (hle : restrictIdeal I U ≤ restrictIdeal J U) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    restrictIdeal (I.comap g) V ≤ restrictIdeal (J.comap g) V := by
  have hf : (Y.homOfLE hV ≫ (g ∣_ U)) ≫ U.ι = V.ι ≫ g := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  rw [restrictIdeal_comap_eq_comap_restrictIdeal g I hf,
    restrictIdeal_comap_eq_comap_restrictIdeal g J hf]
  exact Scheme.IdealSheafData.comap_mono _ hle

/- English proof (authored)
At each point choose the neighborhood supplied by maximal contact. In the coordinate case the hypersurface is already a single coordinate divisor in an étale chart. In the unit case take an étale chart inside the neighborhood, where further restriction still gives the unit ideal. These local forms give a smooth divisor.
-/
theorem IsMaxContactHypersurface.isSmoothDivisor {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] {A : P.IdealSheafData} {μ : ℕ}
    {H : P.IdealSheafData} (h : IsMaxContactHypersurface k p A μ H) :
    IsSmoothDivisor p H := by
  refine isSmoothDivisor_of_locally_coordIdeal H ?_
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  · obtain ⟨U', m, hxU', hU'U, -, ⟨c'⟩⟩ := exists_etaleChart_le p x U hxU
    exact ⟨U', hxU', m, c', Or.inl (restrictIdeal_eq_top_of_le H hU'U htop)⟩
  · exact ⟨U, hxU, n, c, Or.inr ⟨j, hHU⟩⟩

/- English proof (authored)
At a point of the pulled-back hypersurface support take a chart as in the hypothesis. The image point lies in the original hypersurface support, so the original maximal-contact neighborhood gives inclusion of its hypersurface ideal in the maximal-contact ideal there. Shrink the upstairs chart to an affine open contained in the inverse image of that neighborhood. Its hypersurface ideal remains the coordinate ideal, and the pulled-back inclusion puts it inside the upstairs maximal-contact ideal by smooth compatibility. At a point off the pulled-back support, choose an affine neighborhood disjoint from it. The hypersurface ideal is unit there. The upstairs order locus is pulled back from the downstairs order locus, which lies within the downstairs hypersurface support, so this neighborhood also misses the upstairs order locus.
-/
theorem IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal {k : Type u} [Field k] [CharZero k]
    {P Y : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (g : Y ⟶ P) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)] {A : P.IdealSheafData} {μ : ℕ}
    {H : P.IdealSheafData} (h : IsMaxContactHypersurface k p A μ H) (hμ : 1 ≤ μ)
    (hcharts : ∀ y : Y, y ∈ (H.comap g).support →
      ∃ (V : Y.Opens) (n : ℕ) (c : EtaleChart (g ≫ p) V n) (j : Fin n),
        y ∈ V ∧ restrictIdeal (H.comap g) V = c.coordIdeal {j}) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g) := by
  intro y
  by_cases hy : y ∈ (H.comap g).support
  · obtain ⟨V, n, c, j, hyV, hHV⟩ := hcharts y hy
    have hx : g.base y ∈ H.support := (Scheme.IdealSheafData.mem_support_comap ..).mp hy
    obtain ⟨U, hU, hxU, hcase⟩ := h (g.base y)
    have hle : restrictIdeal H U ≤ restrictIdeal (maxContactIdeal k p A μ) U := by
      rcases hcase with ⟨-, htop⟩ | ⟨n₀, c₀, j₀, hHU, hmc⟩
      · exact absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U htop _ hxU)
      · rw [hHU]
        exact hmc
    have hyVU : y ∈ (V ⊓ g ⁻¹ᵁ U : Y.Opens) := ⟨hyV, hxU⟩
    obtain ⟨V', hV'aff, hyV', hV'le⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyVU
    have hV'V : V' ≤ V := le_trans hV'le inf_le_left
    have hV'U : V' ≤ g ⁻¹ᵁ U := le_trans hV'le inf_le_right
    have heq : restrictIdeal (H.comap g) V' = (c.restrict hV'V).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c (H.comap g) {j} hHV
    refine ⟨V', hV'aff, hyV', Or.inr ⟨n, c.restrict hV'V, j, heq, ?_⟩⟩
    have hgoal : (c.restrict hV'V).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal k (g ≫ p) (A.comap g) μ) V' := by
      rw [← heq, maxContactIdeal_comap k p g A μ]
      exact restrictIdeal_comap_le_of_restrictIdeal_le g hle V' hV'U
    exact hgoal
  · have hWopen : IsOpen (((H.comap g).support : Set ↥Y)ᶜ) :=
      (H.comap g).support.2.isOpen_compl
    obtain ⟨V, hVaff, hyV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (show y ∈ (⟨((H.comap g).support : Set ↥Y)ᶜ, hWopen⟩ : Y.Opens) from hy)
    refine ⟨V, hVaff, hyV, Or.inl ⟨?_, ?_⟩⟩
    · rw [Set.disjoint_left]
      intro z hz hzV
      have hz2 := hz
      rw [orderAtLeastLocus_comap k p g A μ] at hz2
      have hz3 : g.base z ∈ H.support := h.orderAtLeastLocus_subset_support hμ hz2
      have hz4 : z ∈ (H.comap g).support :=
        (Scheme.IdealSheafData.mem_support_comap ..).mpr hz3
      exact (hVW hzV) hz4
    · refine (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
      intro z hzV
      exact hVW hzV

/- English proof (authored)
The assumed stability makes the pulled-back hypersurface a smooth divisor. At every point of its support, the coordinate theorem for smooth divisors gives an étale chart where its ideal is a single coordinate ideal. These charts meet the hypothesis of the maximal-contact pullback argument.
-/
theorem IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback {k : Type u} [Field k]
    [CharZero k] {P Y : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p] (g : Y ⟶ P)
    [AlgebraicGeometry.Smooth g] [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)]
    {A : P.IdealSheafData} {μ : ℕ} {H : P.IdealSheafData}
    (hdiv : IsSmoothDivisorStableUnderSmoothPullback.{u})
    (hH : IsSmoothDivisor p H)
    (h : IsMaxContactHypersurface k p A μ H) (hμ : 1 ≤ μ) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g) := by
  refine IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal g h hμ ?_
  intro y hy
  obtain ⟨V, m, c, j, hyV, heq⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (g ≫ p) (H.comap g)
      (hdiv k P Y p g H hH) y hy
  exact ⟨V, m, c, j, hyV, heq⟩

/- English proof (authored)
A maximal-contact hypersurface is a smooth divisor by its local coordinate description. Apply smooth-pullback stability of smooth divisors and the maximal-contact comparison to this hypersurface, at the given positive mark.
-/
theorem maxContactHypersurfaceSmoothPullback_of_isSmoothDivisorStableUnderSmoothPullback
    (hdiv : IsSmoothDivisorStableUnderSmoothPullback.{u}) : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u} := by
  intro k hk hk0 P p hsp hfp Y g hsg hfg A μ hμ H hH
  exact IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback g hdiv
    (IsMaxContactHypersurface.isSmoothDivisor hH) hH hμ

end FunctorialResolution.EmbeddedResolution

end
