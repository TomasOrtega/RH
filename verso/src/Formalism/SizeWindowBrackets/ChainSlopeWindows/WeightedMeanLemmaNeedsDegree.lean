import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

section Means

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Unfold `wmean`. Establish `hS : 0 < ∑ u, d u` using `Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty`. Conclude with `div_le_div_of_nonneg_right (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hXY u) (hd u).le) hS.le`.
-/
theorem wmean_mono' [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ u, 0 < d u)
    (hXY : ∀ u, X u ≤ Y u) : wmean d X ≤ wmean d Y := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hXY u) (hd u).le) hS.le

/- English proof (translation)
Unfold `wmean`. Establish `hS : 0 < ∑ u, d u` using `Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty`. Rewrite using `[← Finset.sum_mul, mul_div_cancel_left₀ _ hS.ne']`.
-/
theorem wmean_const' [Nonempty ι] {d : ι → ℝ} (hd : ∀ u, 0 < d u) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hS.ne']

/- English proof (translation)
Unfold `wmean`. Rewrite using `[← add_div, ← Finset.sum_add_distrib]`. Simplify using `only [mul_add]`.
-/
theorem wmean_add' (d X Y : ι → ℝ) :
    wmean d (fun u => X u + Y u) = wmean d X + wmean d Y := by
  unfold wmean
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [mul_add]

/- English proof (translation)
Unfold `wmean`. Rewrite using `[← sub_div, ← Finset.sum_sub_distrib]`. Simplify using `only [mul_sub]`.
-/
theorem wmean_sub (d X Y : ι → ℝ) :
    wmean d (fun u => X u - Y u) = wmean d X - wmean d Y := by
  unfold wmean
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

end Means

/- English proof (translation)
Introduce `d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2`. Take `⟨hmax, hmu⟩` from `hS2`. Establish `h1 : wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u) ≤ sF d muN h`. Establish `e : wmean d (fun u => (muM u - h u + Sg0) - (dr u + BE u)) = wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u)`. Rewrite using `[wmean_sub d (fun u => muM u - h u + Sg0) (fun u => dr u + BE u), wmean_add' d (fun u => muM u - h u) (fun _ => Sg0), wmean_const' hd]`.

Rewrite using `[← e]`. Unfold `sF`. Conclude with `wmean_mono' hd fun u => by linarith [hmu u]`. Establish `h2 : umax (fun u => muMaxN u - h u) ≤ umax (fun u => muMaxM u - h u) + Sg0`. Unfold `umax`.

Apply `Finset.sup'_le` to reduce the goal to its premises. Introduce `u _`. Establish `: muMaxM u - h u ≤ Finset.univ.sup' Finset.univ_nonempty (fun u => muMaxM u - h u)` using `Finset.le_sup' (fun u => muMaxM u - h u) (Finset.mem_univ u)`. Combine the linear relations using `[hmax u, hdr u]`. Unfold `uF rhsU`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weighted_mean_lemma_ge (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaUge ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2
  obtain ⟨hmax, hmu⟩ := hS2
  have h1 : wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u)
      ≤ sF d muN h := by
    have e : wmean d (fun u => (muM u - h u + Sg0) - (dr u + BE u))
        = wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u) := by
      rw [wmean_sub d (fun u => muM u - h u + Sg0) (fun u => dr u + BE u),
        wmean_add' d (fun u => muM u - h u) (fun _ => Sg0), wmean_const' hd]
    rw [← e]
    unfold sF
    exact wmean_mono' hd fun u => by linarith [hmu u]
  have h2 : umax (fun u => muMaxN u - h u) ≤ umax (fun u => muMaxM u - h u) + Sg0 := by
    unfold umax
    apply Finset.sup'_le
    intro u _
    have : muMaxM u - h u ≤ Finset.univ.sup' Finset.univ_nonempty (fun u => muMaxM u - h u) :=
      Finset.le_sup' (fun u => muMaxM u - h u) (Finset.mem_univ u)
    linarith [hmax u, hdr u]
  unfold uF rhsU
  linarith

/- English proof (translation)
Introduce `d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2`. Conclude with `weighted_mean_lemma_ge ι d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr ⟨hS2.1, fun u => (hS2.2 u).symm.le⟩`.
-/
theorem weighted_mean_claimU (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaU ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2
  exact weighted_mean_lemma_ge ι d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr
    ⟨hS2.1, fun u => (hS2.2 u).symm.le⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun u => if u then 1 else 2, fun _ => 0, fun _ => -1, fun _ => 0, fun _ => 0, fun u => if u then 1 else 0, fun _ => 0, fun _ => 1, 0, 0, 0, 1, fun u => by cases u <;> norm_num, fun _ => le_rfl, ⟨fun _ => by norm_num, fun _ => by norm_num⟩, fun _ => le_rfl, fun _ => by norm_num, …`.
-/
example : ∃ (d muMaxN muN muMaxM muM h dr BE : Bool → ℝ) (Sg0 A A' V : ℝ),
    (∀ u, 0 < d u) ∧ (∀ u, 0 ≤ dr u) ∧ Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 ∧
    (∀ u, muMaxM u ≤ A) ∧ (∀ u, -A' ≤ muM u) ∧ (∀ u u', |h u - h u'| ≤ V) ∧ (∃ u, h u ≠ h (!u)) :=
  ⟨fun u => if u then 1 else 2, fun _ => 0, fun _ => -1, fun _ => 0, fun _ => 0,
    fun u => if u then 1 else 0, fun _ => 0, fun _ => 1, 0, 0, 0, 1,
    fun u => by cases u <;> norm_num, fun _ => le_rfl,
    ⟨fun _ => by norm_num, fun _ => by norm_num⟩, fun _ => le_rfl, fun _ => by norm_num,
    fun u u' => by cases u <;> cases u' <;> norm_num, ⟨true, by norm_num⟩⟩

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
