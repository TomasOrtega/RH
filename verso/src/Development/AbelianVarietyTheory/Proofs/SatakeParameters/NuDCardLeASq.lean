import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NuRowNonnegLeTenMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YoungDiagramCardEqSumRowLenRange
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x1, h1⟩` from `GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm`. Take `⟨x2, h2⟩` from `GlobalTheory.ShNums.size_rel Fm`. Use `⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩` and prove the remaining obligations. Establish `hr` using `h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)`.

Simplify using `only [Nat.add_sub_cancel] at hr`. Take `⟨hkN, -, -, -, -, h4, -, -, -, hS⟩` from `h2 x (le_trans (le_max_right _ _) hx) hx1 i`. Establish `hsx` using `Fm.L_x x i hx1`. Rewrite using `[GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]`. Establish `hsum` using `Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j)) (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b) (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)`.

Rewrite `hsum` using `[Finset.card_range, nsmul_eq_mul]`. Establish `hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m`. Establish `: (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m`. Unfold `Ranks.N`. Use `Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hk : (1 : ℝ) ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ (Fm.D x i).R.k)` after adjusting the coercions.

Establish `hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m` using `Nat.cast_nonneg _`. Establish `hNk` using `le_mul_of_one_le_left hN0 hk`. Establish `heta` using `(Fm.L x i).etaSz_pos`. Establish `hb : 0 < (Fm.L x i).sc.b` using `Real.exp_pos _`. Establish `hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10` using `by linarith`.

Rewrite `h4` using `[hsx]`. Establish `hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b` using `by positivity`. Establish `h5` using `mul_le_mul_of_nonneg_right hN hxb`. Establish `ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b`. Unfold `Scale.a`.

Rewrite using `[hsx]`. Rewrite using `[ha]`. Establish `h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2)` using `le_mul_of_one_le_left (by positivity) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nuD_card_le_a_sq : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  have hr := h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := h2 x (le_trans (le_max_right _ _) hx) hx1 i
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

end GlobalTheory
