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

/- English proof (authored)
Multiplying the pointwise inequality by each positive weight preserves it, and summing gives the numerator inequality. The sum of the weights is positive because the index set is nonempty. Divide by this sum.
-/
theorem wmean_mono' [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ u, 0 < d u)
    (hXY : ∀ u, X u ≤ Y u) : wmean d X ≤ wmean d Y := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hXY u) (hd u).le) hS.le

/- English proof (authored)
Factor the common value out of the numerator. The remaining factor is the sum of the weights, which is positive and cancels the denominator.
-/
theorem wmean_const' [Nonempty ι] {d : ι → ℝ} (hd : ∀ u, 0 < d u) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  unfold wmean
  have hS : 0 < ∑ u, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hS.ne']

/- English proof (authored)
Distribute the weight across each addition in the numerator and split the finite sum. Dividing both terms by the same total weight gives the sum of their means.
-/
theorem wmean_add' (d X Y : ι → ℝ) :
    wmean d (fun u => X u + Y u) = wmean d X + wmean d Y := by
  unfold wmean
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [mul_add]

/- English proof (authored)
Distribute the weight across each difference and split the numerator as a difference of finite weighted sums. Division by the common total weight gives the difference of the two means.
-/
theorem wmean_sub (d X Y : ι → ℝ) :
    wmean d (fun u => X u - Y u) = wmean d X - wmean d Y := by
  unfold wmean
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

end Means

/- English proof (authored)
The pointwise lower bound on the new mean slopes gives, after subtracting the shifts and taking the positive weighted mean, a lower bound by the old shifted mean plus the common gain minus the weighted mean of the combined losses. For the maximum slopes, each new shifted value is at most the corresponding old shifted value plus the common gain because the drop is nonnegative. Taking maxima gives the same upper bound with the old maximum. Subtract the lower bound on the mean from the upper bound on the maximum. The common gain cancels, leaving the old spread plus the weighted mean of the combined losses.
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

/- English proof (authored)
The equality for the mean slopes implies the lower inequality required by the preceding bound. The two versions have the same upper inequality for the maximal slopes and the same positivity hypotheses, so that bound applies.
-/
theorem weighted_mean_claimU (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaU ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2
  exact weighted_mean_lemma_ge ι d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr
    ⟨hS2.1, fun u => (hS2.2 u).symm.le⟩

/- English proof (authored)
Use two indices, with weights 1 and 2 and shifts 1 and 0, respectively. Set both maximal slopes and the old mean slope to zero, and set the new mean slope to −1. Set the common gain and all drops to zero and the remaining loss to one. The two slope inequalities then hold as equalities. Both bounds for the old slopes can be set to zero, and the shift oscillation is exactly one. The shifts differ at the two indices.
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
