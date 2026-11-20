import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

/- English proof (translation)
Introduce `E _ _ _ r X x0 ho k z hz`. Rewrite using `[IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `set x := cpt X x0 z`. Set `L' : ℕ → ℝ` to `fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0`.

Establish `h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1)` using `fun i => by`. Simplify using `only [L', dif_pos (Nat.succ_lt_succ i.isLt)]`. Both sides reduce to the same expression. Establish `h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i` using `fun i => by`. Simplify using `only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]`.

Both sides reduce to the same expression. Establish `hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) = 2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ)` using `fun i => by`. Unfold `laS`. Distinguish the cases in `h : (i : ℕ) < X.p0`. Rewrite using `[if_neg (not_le.2 h), if_pos h]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_pos (not_lt.1 h), if_neg h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hL0 : L' 0 = 0`. Simplify using `only [L', dif_pos (Nat.succ_pos r)]`. Conclude with `IW.Lm_zero X x τ`. Establish `hLr : L' r = 0`. Simplify using `only [L', dif_pos (Nat.lt_succ_self r)]`.

Conclude with `IW.Lm_last_cpt X x0 ho z τ`. Establish `hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖`. Simplify using `only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]`. Both sides reduce to the same expression. Repeatedly rewrite using `[h1, h2, hk]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]`. Establish `hsplit : ∑ i ∈ Finset.range r, (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) = 2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) - (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phla_laS_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 →
    phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  intro E _ _ _ r X x0 ho k z hz
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) =
      2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ) := fun i => by
    unfold laS
    by_cases h : (i : ℕ) < X.p0
    · rw [if_neg (not_le.2 h), if_pos h]; push_cast; ring
    · rw [if_pos (not_lt.1 h), if_neg h]; push_cast; ring
  have hL0 : L' 0 = 0 := by
    simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]
  have hsplit : ∑ i ∈ Finset.range r,
      (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) =
      2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) -
        (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]
  ring

end GlobalTheory.ScalarPoin
