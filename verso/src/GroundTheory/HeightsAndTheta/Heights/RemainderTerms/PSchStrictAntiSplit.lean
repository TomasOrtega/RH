import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddGapLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd`.
-/
theorem SchStrictAntiSplit.add_gap_le {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i :=
  _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]`.
-/
theorem SchStrictAntiSplit.sum_staircase (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]

/- English proof (translation)
Introduce `r n d hd hsum`. Establish `hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i`. Introduce `i`. Establish `hr : 0 < r` using `Fin.pos i`. Establish `h` using `SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩ (by simp; omega)`.

Use linear arithmetic over natural numbers and integers. Use `⟨hlow, ?_⟩` and prove the remaining obligations. Rewrite using `[partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) = ∑ i : Fin r, d i`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)`. Rewrite `hadd` using `[SchStrictAntiSplit.sum_staircase]`. Use linear arithmetic over natural numbers and integers. Introduce `i j hij`.

Establish `h` using `SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)`. Use `hlow i` as an intermediate fact. Use `hlow j` as an intermediate fact. Establish `: (i : ℕ) ≤ j` using `hij`. Establish `: (j : ℕ) < r` using `j.isLt`.

Use `show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))`. Use linear arithmetic over natural numbers and integers.
-/
theorem SchStrictAntiSplit.proof : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega

end GroundTheory.Heights₂.Heights.RestTerms
