import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

open Filter Topology in

/- English proof (translation)
Use `set f : ℂ → ℂ := fun z => L.weierstrassP z - L'.weierstrassP z with hf`. Establish `hm : MeromorphicOn f Set.univ` using `fun z _ => (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)`. Establish `h0 : meromorphicOrderAt f 0 = ⊤`. Rewrite using `[meromorphicOrderAt_eq_top_iff]`. Use `filter_upwards [h] with z hz`.

Simplify using `[hf, hz]`. Establish `hx : meromorphicOrderAt f x = ⊤`. Assume the negation of the conclusion as `hne`. Use `(hm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1 ⟨⟨x, Set.mem_univ _⟩, hne⟩ ⟨0, Set.mem_univ _⟩` as an intermediate fact. Conclude with `this h0`.

Rewrite `hx` using `[meromorphicOrderAt_eq_top_iff]`. Use `filter_upwards [hx] with z hz`. Conclude with `sub_eq_zero.1 hz`.
-/
theorem weierstrassP_eventuallyEq_nhdsNE_of_zero (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) (x : ℂ) :
    L.weierstrassP =ᶠ[𝓝[≠] x] L'.weierstrassP := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - L'.weierstrassP z with hf
  have hm : MeromorphicOn f Set.univ := fun z _ =>
    (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)
  have h0 : meromorphicOrderAt f 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hf, hz]
  have hx : meromorphicOrderAt f x = ⊤ := by
    by_contra hne
    have := (hm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, Set.mem_univ _⟩, hne⟩ ⟨0, Set.mem_univ _⟩
    exact this h0
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with z hz
  exact sub_eq_zero.1 hz

open Filter Topology in

/- English proof (translation)
Introduce `l hl`. Assume the negation of the conclusion as `hl'`. Establish `h1` using `L.order_weierstrassP l hl`. Establish `h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP l` using `(L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg`. Rewrite `h2` using `[← meromorphicOrderAt_congr (weierstrassP_eventuallyEq_nhdsNE_of_zero L L' h l), h1]`.

Conclude with `absurd h2 (by decide)`.
-/
theorem lattice_subset_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) ⊆ L'.lattice := by
  intro l hl
  by_contra hl'
  have h1 := L.order_weierstrassP l hl
  have h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP l :=
    (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr (weierstrassP_eventuallyEq_nhdsNE_of_zero L L' h l), h1] at h2
  exact absurd h2 (by decide)

open Filter Topology in

/- English proof (translation)
The claim follows from `Set.Subset.antisymm (lattice_subset_of_weierstrassP L L' h) (lattice_subset_of_weierstrassP L' L h.symm)`.
-/
theorem lattice_eq_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) = L'.lattice :=
  Set.Subset.antisymm (lattice_subset_of_weierstrassP L L' h)
    (lattice_subset_of_weierstrassP L' L h.symm)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
