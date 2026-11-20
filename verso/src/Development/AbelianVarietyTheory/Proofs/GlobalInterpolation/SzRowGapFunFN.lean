import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hx0 : 0 ≤ x` using `by linarith`. Establish `h5 : x ^ 5 ≤ x ^ 401` using `pow_le_pow_right₀ hx1 (by norm_num)`. Establish `h7 : (7 : ℝ) ≤ x ^ 401`. Establish `: x ^ 2 ≤ x ^ 401` using `pow_le_pow_right₀ hx1 (by norm_num)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h402 : x ^ 401 ≤ x ^ 402` using `pow_le_pow_right₀ hx1 (by norm_num)`. Establish `hA : k + m * (t + (r + 6) + 1) ≤ x ^ 403`. Establish `h1 : m * (t + (r + 6) + 1) ≤ x * (3 * x ^ 401)` using `mul_le_mul hm (by linarith) (by positivity) hx0`. Establish `h2 : x * (3 * x ^ 401) = 3 * x ^ 402` using `by ring`.

Establish `h3 : 4 * x ^ 402 ≤ x * x ^ 402` using `mul_le_mul_of_nonneg_right hx (by positivity)`. Establish `h4 : x * x ^ 402 = x ^ 403` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA3 : (k + m * (t + (r + 6) + 1)) ^ 3 ≤ (x ^ 403) ^ 3` using `pow_le_pow_left₀ (by positivity) hA 3`. Establish `e1 : (x ^ 403) ^ 3 = x ^ 1209` using `by rw [← pow_mul]`.

Establish `h9 : x ^ 401 ≤ x ^ 1209` using `pow_le_pow_right₀ hx1 (by norm_num)`. Establish `h1 : (1 : ℝ) ≤ x ^ 1209` using `one_le_pow₀ hx1`. Establish `h3 : 4 * x ^ 1209 ≤ x * x ^ 1209` using `mul_le_mul_of_nonneg_right hx (by positivity)`. Establish `h4 : x * x ^ 1209 = x ^ 1210` using `(pow_succ' x 1209).symm`. Rewrite `hA3` using `[e1]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_cube_bound (x t k m r : ℝ) (hx : 4 ≤ x) (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r)
    (ht : t ≤ x ^ 401) (hk : k ≤ x ^ 5) (hm : m ≤ x) (hr : r ≤ x ^ 5) :
    t + 2 * (k + m * (t + (r + 6) + 1)) ^ 3 + 1 ≤ x ^ 1210 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
  have h7 : (7 : ℝ) ≤ x ^ 401 := by
    have : x ^ 2 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have h402 : x ^ 401 ≤ x ^ 402 := pow_le_pow_right₀ hx1 (by norm_num)
  have hA : k + m * (t + (r + 6) + 1) ≤ x ^ 403 := by
    have h1 : m * (t + (r + 6) + 1) ≤ x * (3 * x ^ 401) :=
      mul_le_mul hm (by linarith) (by positivity) hx0
    have h2 : x * (3 * x ^ 401) = 3 * x ^ 402 := by ring
    have h3 : 4 * x ^ 402 ≤ x * x ^ 402 := mul_le_mul_of_nonneg_right hx (by positivity)
    have h4 : x * x ^ 402 = x ^ 403 := by ring
    linarith
  have hA3 : (k + m * (t + (r + 6) + 1)) ^ 3 ≤ (x ^ 403) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA 3
  have e1 : (x ^ 403) ^ 3 = x ^ 1209 := by rw [← pow_mul]
  have h9 : x ^ 401 ≤ x ^ 1209 := pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : (1 : ℝ) ≤ x ^ 1209 := one_le_pow₀ hx1
  have h3 : 4 * x ^ 1209 ≤ x * x ^ 1209 := mul_le_mul_of_nonneg_right hx (by positivity)
  have h4 : x * x ^ 1209 = x ^ 1210 := (pow_succ' x 1209).symm
  rw [e1] at hA3
  linarith

/- English proof (translation)
Introduce `eps he0 he1 C hC`. Establish `hCN : 1 ≤ C.P.Ch0N` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])`. Take `⟨x0, hx0⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1`. Use `⟨0, fun cD _ => ⟨max 1210 (3 + 402 * C.P.Ch0N), fun ch hch => ⟨max x0 4, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D L hε hx hV`.

Establish `hx4 : 4 ≤ L.sc.x` using `le_trans (le_max_right _ _) hx`. Establish `hx1 : 1 ≤ L.sc.x` using `by linarith`. Establish `hxp : 0 < L.sc.x` using `by linarith`. Take `⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, hm1, -⟩` from `hx0 L.sc D.R hε (le_trans (le_max_left _ _) hx) hV.ranks`. Establish `hmp : (0 : ℝ) < D.R.m` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hm1`.

Establish `hh : L.sc.x ^ ch ≤ h0 L`. Establish `e : h0 L = (h0v L.sc ch : ℝ)`. Unfold `h0`. Rewrite using `[hV.eta_eq]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Unfold `h0v`. Use `push_cast`. Establish `h1` using `Nat.le_ceil (L.sc.x ^ ch)`. Establish `h2 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Establish `ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401` using `by exact_mod_cast ht`. Establish `hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5` using `by exact_mod_cast hr`. Establish `hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5` using `le_trans (by exact_mod_cast hkr) hr'`.

Establish `h1` using `gap_cube_bound L.sc.x D.R.t D.R.k D.R.m D.R.r hx4 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht' hk' hm hr'`. Establish `h2 : L.sc.x ^ ((1210 : ℕ) : ℝ) ≤ L.sc.x ^ ch` using `Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (by push_cast; exact le_max_left _ _) hch)`. Rewrite `h2` using `[Real.rpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ (L.sc.x ^ (402 : ℝ)) ^ C.P.Ch0N` using `Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)`.

Rewrite `h1` using `[← Real.rpow_mul hxp.le]`. Establish `h2 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ L.sc.x ^ (3 : ℝ) * L.sc.x ^ (402 * C.P.Ch0N)` using `mul_le_mul hf h1 (by positivity) (by positivity)`. Rewrite `h2` using `[← Real.rpow_add hxp]`. Establish `h3 : L.sc.x ^ (3 + 402 * C.P.Ch0N) ≤ L.sc.x ^ ch` using `Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (le_max_right _ _) hch)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem szRow_gap_fun_fN : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  intro eps he0 he1 C hC
  have hCN : 1 ≤ C.P.Ch0N := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD _ => ⟨max 1210 (3 + 402 * C.P.Ch0N), fun ch hch => ⟨max x0 4, ?_⟩⟩⟩
  intro D L hε hx hV
  have hx4 : 4 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, hm1, -⟩ :=
    hx0 L.sc D.R hε (le_trans (le_max_left _ _) hx) hV.ranks
  have hmp : (0 : ℝ) < D.R.m := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hm1
  have hh : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [hV.eta_eq]
      field_simp
    rw [e]
    unfold h0v
    push_cast
    have h1 := Nat.le_ceil (L.sc.x ^ ch)
    have h2 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by exact_mod_cast ht
    have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by exact_mod_cast hr
    have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
    have h1 := gap_cube_bound L.sc.x D.R.t D.R.k D.R.m D.R.r hx4 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht' hk' hm hr'
    have h2 : L.sc.x ^ ((1210 : ℕ) : ℝ) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (by push_cast; exact le_max_left _ _) hch)
    rw [Real.rpow_natCast] at h2
    linarith
  · have h1 : (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ (L.sc.x ^ (402 : ℝ)) ^ C.P.Ch0N :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
    rw [← Real.rpow_mul hxp.le] at h1
    have h2 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ L.sc.x ^ (3 : ℝ) * L.sc.x ^ (402 * C.P.Ch0N) :=
      mul_le_mul hf h1 (by positivity) (by positivity)
    rw [← Real.rpow_add hxp] at h2
    have h3 : L.sc.x ^ (3 + 402 * C.P.Ch0N) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (le_max_right _ _) hch)
    linarith

end GlobalTheory.EX
