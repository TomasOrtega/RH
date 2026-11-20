import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

/- English proof (translation)
Establish `hle : i.ker ≤ g.ker`. Use `(Scheme.IdealSheafData.le_ofIdeals_iff (I := i.ker)).mpr ?_` and prove the remaining obligations. Introduce `U a ha`. Rewrite using `[RingHom.mem_ker]`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises.

Rewrite using `[← Scheme.preimage_basicOpen]`. Use extensionality with `t`. Simplify using `only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Introduce `ht`. Establish `h1` using `(Scheme.IdealSheafData.mem_support_iff.mp (hg t)) U`.

Conclude with `(Y.mem_zeroLocus_iff _ _).mp h1 a ha ht`. Conclude with `⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac _ _ _⟩`.
-/
theorem GlobalTheory.lift_of_reduced_of_support {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (g : T ⟶ Y) (hg : ∀ t, g t ∈ i.ker.support) : ∃ h : T ⟶ X, h ≫ i = g := by
  have hle : i.ker ≤ g.ker := by
    refine (Scheme.IdealSheafData.le_ofIdeals_iff (I := i.ker)).mpr ?_
    intro U a ha
    rw [RingHom.mem_ker]
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro ht
    have h1 := (Scheme.IdealSheafData.mem_support_iff.mp (hg t)) U
    exact (Y.mem_zeroLocus_iff _ _).mp h1 a ha ht
  exact ⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac _ _ _⟩
