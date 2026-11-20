import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DominationDegreeFormOfReading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

section Segre

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

def segreCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Ω := ∏ k, y ⟨k, c k⟩

omit [DecidableEq K] in

/- English proof (translation)
Unfold `segreCoord`. Rewrite using `[Finset.prod_ne_zero_iff]`. Simplify using the standard rewrite rules.
-/
theorem segreCoord_ne_zero_iff (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreCoord y c ≠ 0 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  unfold segreCoord
  rw [Finset.prod_ne_zero_iff]
  simp

/- English proof (translation)
Unfold `segreCoord`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k), ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]`. Establish `hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k i k'⟩ = ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩`. Use `Finset.prod_congr rfl fun k' hk' => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hk')]`.

Establish `hne : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k' _ => hc k'`. Simplify using `only [Function.update_self]`. Rewrite using `[hrest, mul_div_mul_right _ _ hne]`.
-/
theorem segreCoord_update_div (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    segreCoord y (Function.update c k i) / segreCoord y c = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  unfold segreCoord
  rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
  have hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k i k'⟩ =
      ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hne : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => hc k'
  simp only [Function.update_self]
  rw [hrest, mul_div_mul_right _ _ hne]

variable (R : Type) [CommRing R] [Algebra R Ω]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `chartRingOver`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`. Establish `h` using `segreCoord_update_div y c hc k i`.

Simplify using `only at h ⊢`. Rewrite using `[← h]`. Conclude with `Algebra.subset_adjoin ⟨⟨(), Function.update c k i⟩, rfl⟩`. Use `conv_lhs => unfold chartRingOver`. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce and unpack `_ ⟨⟨u, d⟩, rfl⟩`. Use `show segreCoord y d / segreCoord y c ∈ chartRingOver R y c`. Unfold `segreCoord`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, d k⟩, rfl⟩`.
-/
theorem chartRingOver_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    chartRingOver R y c = chartRingOver R (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (segreCoord y)) (fun _ => c) := by
  apply le_antisymm
  · unfold chartRingOver
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    have h := segreCoord_update_div y c hc k i
    simp only at h ⊢
    rw [← h]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update c k i⟩, rfl⟩
  · conv_lhs => unfold chartRingOver
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨u, d⟩, rfl⟩
    show segreCoord y d / segreCoord y c ∈ chartRingOver R y c
    unfold segreCoord
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, d k⟩, rfl⟩

/- English proof (translation)
Apply `sameModel_of_charts` to reduce the goal to its premises. Introduce `c hc`. Use `⟨fun _ => c, fun _ => (segreCoord_ne_zero_iff y c).mpr hc, chartRingOver_segre R y c hc⟩` and prove the remaining obligations. Introduce `c' hc'`. Establish `hc : ∀ k, y ⟨k, c' () k⟩ ≠ 0` using `(segreCoord_ne_zero_iff y (c' ())).mp (hc' ())`.

Conclude with `⟨c' (), hc, chartRingOver_segre R y (c' ()) hc⟩`.
-/
theorem sameModel_segreCoord (y : (Σ k, ι k) → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.SameModel R y (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (segreCoord y)) := by
  apply sameModel_of_charts
  · intro c hc
    refine ⟨fun _ => c, fun _ => (segreCoord_ne_zero_iff y c).mpr hc, chartRingOver_segre R y c hc⟩
  · intro c' hc'
    have hc : ∀ k, y ⟨k, c' () k⟩ ≠ 0 := (segreCoord_ne_zero_iff y (c' ())).mp (hc' ())
    exact ⟨c' (), hc, chartRingOver_segre R y (c' ()) hc⟩

end Segre

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ y hy`. Use `choose c₀ hc₀ using hy`. Establish `hpos : 0 < Fintype.card (∀ k, ι k)` using `Fintype.card_pos_iff.mpr ⟨c₀⟩`. Set `e : (∀ k, ι k) ≃ Fin (Fintype.card (∀ k, ι k) - 1 + 1)` to `(Fintype.equivFin _).trans (finCongr (by omega))`. Use `⟨Fintype.card (∀ k, ι k) - 1, e, segreCoord y ∘ e.symm, fun c => by simp [segreCoord], ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Establish `h1` using `congrFun h0 (e c₀)`. Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1`. Conclude with `(segreCoord_ne_zero_iff y c₀).mpr hc₀ h1`. Introduce `R _ _`.

Conclude with `(sameModel_segreCoord R y).trans (sameModel_reindex R (segreCoord y) e)`.
-/
theorem SegreModel.full : SegreModel.Statement := by
  intro K _ _ ι _ _ Ω _ y hy
  classical
  choose c₀ hc₀ using hy
  have hpos : 0 < Fintype.card (∀ k, ι k) := Fintype.card_pos_iff.mpr ⟨c₀⟩
  let e : (∀ k, ι k) ≃ Fin (Fintype.card (∀ k, ι k) - 1 + 1) :=
    (Fintype.equivFin _).trans (finCongr (by omega))
  refine ⟨Fintype.card (∀ k, ι k) - 1, e, segreCoord y ∘ e.symm, fun c => by simp [segreCoord], ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 (e c₀)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1
    exact (segreCoord_ne_zero_iff y c₀).mpr hc₀ h1
  · intro R _ _
    exact (sameModel_segreCoord R y).trans (sameModel_reindex R (segreCoord y) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
