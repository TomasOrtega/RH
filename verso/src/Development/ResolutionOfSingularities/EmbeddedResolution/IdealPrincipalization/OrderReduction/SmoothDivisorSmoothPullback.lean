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

/- English proof (translation)
Rewrite using `[restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hf]`.
-/
private theorem restrictIdeal_comap_eq_comap_restrictIdeal {P Y : Scheme.{u}} (g : Y ⟶ P)
    (I : P.IdealSheafData) {U : P.Opens} {V : Y.Opens} {f : V.toScheme ⟶ U.toScheme}
    (hf : f ≫ U.ι = V.ι ≫ g) :
    restrictIdeal (I.comap g) V = (restrictIdeal I U).comap f := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hf]

/- English proof (translation)
Establish `hf : (Y.homOfLE hV ≫ (g ∣_ U)) ≫ U.ι = V.ι ≫ g`. Rewrite using `[Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]`. Rewrite using `[restrictIdeal_comap_eq_comap_restrictIdeal g I hf, restrictIdeal_comap_eq_comap_restrictIdeal g J hf]`. Conclude with `Scheme.IdealSheafData.comap_mono _ hle`.
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

/- English proof (translation)
Use `isSmoothDivisor_of_locally_coordIdeal H ?_` and prove the remaining obligations. Introduce `x`. Take `⟨U, hU, hxU, hcase⟩` from `h x`. Break down `hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩` into its components or cases. Take `⟨U', m, hxU', hU'U, -, ⟨c'⟩⟩` from `exists_etaleChart_le p x U hxU`.

Conclude with `⟨U', hxU', m, c', Or.inl (restrictIdeal_eq_top_of_le H hU'U htop)⟩`. Conclude with `⟨U, hxU, n, c, Or.inr ⟨j, hHU⟩⟩`.
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

/- English proof (translation)
Introduce `y`. Distinguish the cases in `hy : y ∈ (H.comap g).support`. Take `⟨V, n, c, j, hyV, hHV⟩` from `hcharts y hy`. Establish `hx : g.base y ∈ H.support` using `(Scheme.IdealSheafData.mem_support_comap ..).mp hy`. Take `⟨U, hU, hxU, hcase⟩` from `h (g.base y)`.

Establish `hle : restrictIdeal H U ≤ restrictIdeal (maxContactIdeal k p A μ) U`. Break down `hcase with ⟨-, htop⟩ | ⟨n₀, c₀, j₀, hHU, hmc⟩` into its components or cases. Conclude with `absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U htop _ hxU)`. Rewrite using `[hHU]`. Conclude with `hmc`.

Establish `hyVU : y ∈ (V ⊓ g ⁻¹ᵁ U : Y.Opens)` using `⟨hyV, hxU⟩`. Take `⟨V', hV'aff, hyV', hV'le⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyVU`. Establish `hV'V : V' ≤ V` using `le_trans hV'le inf_le_left`. Establish `hV'U : V' ≤ g ⁻¹ᵁ U` using `le_trans hV'le inf_le_right`. Establish `heq : restrictIdeal (H.comap g) V' = (c.restrict hV'V).coordIdeal {j}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c (H.comap g) {j} hHV`.

Use `⟨V', hV'aff, hyV', Or.inr ⟨n, c.restrict hV'V, j, heq, ?_⟩⟩` and prove the remaining obligations. Establish `hgoal : (c.restrict hV'V).coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k (g ≫ p) (A.comap g) μ) V'`. Rewrite using `[← heq, maxContactIdeal_comap k p g A μ]`. Conclude with `restrictIdeal_comap_le_of_restrictIdeal_le g hle V' hV'U`. Conclude with `hgoal`.

Establish `hWopen : IsOpen (((H.comap g).support : Set ↥Y)ᶜ)` using `(H.comap g).support.2.isOpen_compl`. Take `⟨V, hVaff, hyV, hVW⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show y ∈ (⟨((H.comap g).support : Set ↥Y)ᶜ, hWopen⟩ : Y.Opens) from hy)`. Use `⟨V, hVaff, hyV, Or.inl ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`. Introduce `z hz hzV`.

Establish `hz2` using `hz`. Rewrite `hz2` using `[orderAtLeastLocus_comap k p g A μ]`. Establish `hz3 : g.base z ∈ H.support` using `h.orderAtLeastLocus_subset_support hμ hz2`. Establish `hz4 : z ∈ (H.comap g).support` using `(Scheme.IdealSheafData.mem_support_comap ..).mpr hz3`. Conclude with `(hVW hzV) hz4`.

Use `(FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_` and prove the remaining obligations. Introduce `z hzV`. Conclude with `hVW hzV`.
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

/- English proof (translation)
Use `IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal g h hμ ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨V, m, c, j, hyV, heq⟩` from `exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (g ≫ p) (H.comap g) (hdiv k P Y p g H hH) y hy`. Conclude with `⟨V, m, c, j, hyV, heq⟩`.
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

/- English proof (translation)
Introduce `k hk hk0 P p hsp hfp Y g hsg hfg A μ hμ H hH`. Conclude with `IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback g hdiv (IsMaxContactHypersurface.isSmoothDivisor hH) hH hμ`.
-/
theorem maxContactHypersurfaceSmoothPullback_of_isSmoothDivisorStableUnderSmoothPullback
    (hdiv : IsSmoothDivisorStableUnderSmoothPullback.{u}) : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u} := by
  intro k hk hk0 P p hsp hfp Y g hsg hfg A μ hμ H hH
  exact IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback g hdiv
    (IsMaxContactHypersurface.isSmoothDivisor hH) hH hμ

end FunctorialResolution.EmbeddedResolution

end
