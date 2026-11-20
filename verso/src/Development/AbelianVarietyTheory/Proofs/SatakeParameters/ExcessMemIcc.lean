import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemTopPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockRowsMemIcc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YoungDiagramCardEqSumRowLenRange
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ExcessLow

/- English proof (translation)
Establish `hk' : (2 : ℝ) ≤ k` using `by exact_mod_cast hk`. Rewrite using `[Finset.sum_range_add]`. Establish `b0 : 0 ≤ ∑ r ∈ Finset.range M, f (k + r)` using `Finset.sum_nonneg fun r hr => (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).1`. Establish `b1 : ∑ r ∈ Finset.range M, f (k + r) ≤ M * η`. Use `Finset.sum_le_card_nsmul (Finset.range M) (fun r => f (k + r)) η fun r hr => (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).2` as an intermediate fact.

Simplify using `using this`. Establish `l0 : (k : ℝ) * (w - N - 1 / 2) ≤ ∑ r ∈ Finset.range k, f r`. Use `Finset.card_nsmul_le_sum (Finset.range k) f (w - N - 1 / 2) fun r hr => (hlong r (Finset.mem_range.1 hr)).1.le` as an intermediate fact. Simplify `this` using `only [Finset.card_range, nsmul_eq_mul]`. Establish `l1 : ∑ r ∈ Finset.range k, f r ≤ k * (w + S) + 2 * S`.

Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Finset.sum_range_succ']`. Establish `h0` using `(hlong 0 (by omega)).2`. Rewrite `h0` using `[if_pos rfl]`. Establish `h1` using `Finset.sum_le_card_nsmul (Finset.range k') (fun r => f (r + 1)) (w + S) fun r hr => by`.

Use `(hlong (r + 1) (by have := Finset.mem_range.1 hr; omega)).2` as an intermediate fact. Rewrite `this` using `[if_neg (by omega)]`. Conclude with `this.le`. Simplify using `only [Finset.card_range, nsmul_eq_mul] at h1`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2S : 2 * S ≤ k * S` using `mul_le_mul_of_nonneg_right hk' hS`. Establish `hkN1 : (k : ℝ) ≤ k * N` using `le_mul_of_one_le_right (by linarith) hN1`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem excess_sum (f : ℕ → ℝ) (k M : ℕ) (w N S η W : ℝ) (hk : 2 ≤ k) (hN1 : 1 ≤ N) (hS : 0 ≤ S)
    (hlong : ∀ r < k, w - N - 1 / 2 < f r ∧ f r < w + (if r = 0 then 3 * S else S))
    (hblock : ∀ r, k ≤ r → r < k + M → 0 ≤ f r ∧ f r ≤ η)
    (hkN : (k : ℝ) * N ≤ S / 4) (hkS : (k : ℝ) * S ≤ W) (hM : (M : ℝ) * η ≤ W) (hW : W ≤ w) :
    0 ≤ ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ∧
      ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ≤ 4 * w := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Finset.sum_range_add]
  have b0 : 0 ≤ ∑ r ∈ Finset.range M, f (k + r) :=
    Finset.sum_nonneg fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).1
  have b1 : ∑ r ∈ Finset.range M, f (k + r) ≤ M * η := by
    have := Finset.sum_le_card_nsmul (Finset.range M) (fun r => f (k + r)) η fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).2
    simpa using this
  have l0 : (k : ℝ) * (w - N - 1 / 2) ≤ ∑ r ∈ Finset.range k, f r := by
    have := Finset.card_nsmul_le_sum (Finset.range k) f (w - N - 1 / 2) fun r hr =>
      (hlong r (Finset.mem_range.1 hr)).1.le
    simpa only [Finset.card_range, nsmul_eq_mul] using this
  have l1 : ∑ r ∈ Finset.range k, f r ≤ k * (w + S) + 2 * S := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 := (hlong 0 (by omega)).2
    rw [if_pos rfl] at h0
    have h1 := Finset.sum_le_card_nsmul (Finset.range k') (fun r => f (r + 1)) (w + S) fun r hr => by
      have := (hlong (r + 1) (by have := Finset.mem_range.1 hr; omega)).2
      rw [if_neg (by omega)] at this
      exact this.le
    simp only [Finset.card_range, nsmul_eq_mul] at h1
    push_cast
    nlinarith
  have h2S : 2 * S ≤ k * S := mul_le_mul_of_nonneg_right hk' hS
  have hkN1 : (k : ℝ) ≤ k * N := le_mul_of_one_le_right (by linarith) hN1
  constructor
  · nlinarith
  · nlinarith

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x1, h1⟩` from `GlobalTheory.ShNums.size_rel Fm`. Take `⟨x2, h2⟩` from `GlobalTheory.Ggeo.wPl_windows Fm`. Take `⟨x3, h3⟩` from `GlobalTheory.LongRows.longRows Fm`. Take `⟨x4, h4⟩` from `GlobalTheory.blockRows_mem_Icc Fm`.

Use `⟨max (max x1 x2) (max x3 x4), fun x hx hx1 i u j hj z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [ge_iff_le, max_le_iff] at hx`. Take `⟨⟨e1, e2⟩, e3, e4⟩` from `hx`. Take `⟨a1, a2, a3, -⟩` from `h1 x e1 hx1 i`. Establish `hk` using `(Fm.D x i).R.m_add_three_le_k`.

Rewrite using `[GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]`. Establish `heta` using `(Fm.L x i).etaSz_pos`. Use `excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _ ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le (fun r hr => (h3 x e3 hx1 i u j hj z r hr).1 hz) (fun r hr hr' => h4 x e4 hx1 i u j hj z r …` and prove the remaining obligations. Establish `: 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m`. Unfold `Ranks.N`.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Use `le_trans ?_ a3` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ heta.le` to reduce the goal to its premises. Use `push_cast`.

Establish `: (j : ℝ) ≤ (Fm.D x i).R.m` using `by exact_mod_cast hj.le`. Conclude with `mul_le_mul_of_nonneg_right this (by positivity)`.
-/
theorem excess_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max x1 x2) (max x3 x4), fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hx
  obtain ⟨a1, a2, a3, -⟩ := h1 x e1 hx1 i
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (h3 x e3 hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => h4 x e4 hx1 i u j hj z r hr hr') a1 a2 ?_ (h2 x e2 hx1 i j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

end GlobalTheory.ExcessLow
