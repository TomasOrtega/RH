import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqLat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEq
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEqNhdsNEOfZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_periodPair_of_isLat Λ hΛ`. Take `⟨L', hL'⟩` from `exists_periodPair_of_isLat Λ' hΛ'`. Take `⟨a2, a3⟩` from `g2_g3_eq_periodPair Λ L hL`. Take `⟨b2, b3⟩` from `g2_g3_eq_periodPair Λ' L' hL'`. Establish `e : (L.lattice : Set ℂ) = L'.lattice` using `lattice_eq_of_weierstrassP L L' (weierstrassP_eventuallyEq L L' (by rw [← a2, ← b2, h2]) (by rw [← a3, ← b3, h3]))`.

Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[← hL, ← hL', e]`.
-/
theorem uniqLat_holds (Λ Λ' : AddSubgroup ℂ) (hΛ : IsLat Λ) (hΛ' : IsLat Λ')
    (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ') (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ') : Λ = Λ' := by
  obtain ⟨L, hL⟩ := exists_periodPair_of_isLat Λ hΛ
  obtain ⟨L', hL'⟩ := exists_periodPair_of_isLat Λ' hΛ'
  obtain ⟨a2, a3⟩ := g2_g3_eq_periodPair Λ L hL
  obtain ⟨b2, b3⟩ := g2_g3_eq_periodPair Λ' L' hL'
  have e : (L.lattice : Set ℂ) = L'.lattice :=
    lattice_eq_of_weierstrassP L L'
      (weierstrassP_eventuallyEq L L' (by rw [← a2, ← b2, h2]) (by rw [← a3, ← b3, h3]))
  apply SetLike.coe_injective
  rw [← hL, ← hL', e]

/- English proof (translation)
Unfold `UniqLat`. Introduce `Λ Λ' hΛ hΛ' h2 h3`. Conclude with `uniqLat_holds Λ Λ' hΛ hΛ' h2 h3`.
-/
theorem uniqLat : UniqLat := by
  unfold UniqLat
  intro Λ Λ' hΛ hΛ' h2 h3
  exact uniqLat_holds Λ Λ' hΛ hΛ' h2 h3

/- English proof (translation)
Unfold `UniqInv`. Introduce `Λ Λ' hd h2 h3`. Establish `hd' : Formalism.MainNotions.TaylorLogMetric.discr Λ' ≠ 0`. Unfold `Formalism.MainNotions.TaylorLogMetric.discr at hd ⊢`. Rewrite using `[← h2, ← h3]`.

Conclude with `hd`. Conclude with `uniqLat_holds Λ Λ' (latOfDiscr_holds Λ hd) (latOfDiscr_holds Λ' hd') h2 h3`.
-/
theorem uniqInv_holds : UniqInv := by
  unfold UniqInv
  intro Λ Λ' hd h2 h3
  have hd' : Formalism.MainNotions.TaylorLogMetric.discr Λ' ≠ 0 := by
    unfold Formalism.MainNotions.TaylorLogMetric.discr at hd ⊢
    rw [← h2, ← h3]
    exact hd
  exact uniqLat_holds Λ Λ' (latOfDiscr_holds Λ hd) (latOfDiscr_holds Λ' hd') h2 h3

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
