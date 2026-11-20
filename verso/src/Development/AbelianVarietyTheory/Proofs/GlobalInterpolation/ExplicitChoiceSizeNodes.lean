import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps he0 he1 C _`. Take `⟨x1, hx1⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1`. Use `⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩` and prove the remaining obligations. Simplify using `only [max_le_iff, ge_iff_le] at hx hch`. Take `⟨hxa, hxb⟩` from `hx`.

Take `⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩` from `hx1 L.sc D.R hε hxa hV.ranks`. Establish `hxone : 1 ≤ L.sc.x` using `by linarith`. Establish `hxpos : 0 < L.sc.x` using `by linarith`. Establish `cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a` using `fun a => Real.rpow_natCast _ _`. Establish `hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3` using `by rw [← cast]; exact_mod_cast hf`.

Establish `hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5` using `by rw [← cast]; exact_mod_cast hr`. Establish `ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401` using `by rw [← cast]; exact_mod_cast ht`. Establish `hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402` using `by rw [← cast]; exact_mod_cast hN`. Establish `hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5` using `le_trans (by exact_mod_cast hkr) hr'`. Establish `hnf : (D.R.n : ℝ) ≤ D.R.f`.

Establish `: D.R.n ≤ D.R.f` using `by unfold Ranks.f; omega`. Conclude with `this` after adjusting the coercions. Establish `hm2` using `D.R.two_le_m`. Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m`.

Establish `: D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m`. Unfold `Ranks.N Ranks.r`. Rewrite using `[Nat.mul_add, Nat.mul_one]`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.

Establish `hY : 1 ≤ L.sc.x ^ cD` using `Real.one_le_rpow hxone hcD`. Establish `hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD`. Use `Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)` as an intermediate fact. Unfold `Delv`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ))`. Rewrite using `[L.Sc_eq, hV.Del_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hS0 : 0 ≤ L.Sc` using `by rw [hSc]; positivity`.

Establish `hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD`. Rewrite using `[hSc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m`. Establish `e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ)`.

Rewrite using `[hV.eta_eq]`. Clear the denominators using the available nonvanishing facts. Use `Nat.le_ceil (L.sc.x ^ ch)` as an intermediate fact. Establish `h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ)` using `Nat.cast_nonneg _`. Rewrite using `[e]`.

Unfold `h0v`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m`. Use `le_trans ?_ hh0` and prove the remaining obligations.

Rewrite using `[← cast, ← Real.rpow_add hxpos]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)`. Establish `hth : L.sc.x ^ szTh L ≤ L.sc.x`. Establish `: szTh L ≤ 1` using `by unfold szTh; rw [hε]; linarith`. Simplify using `using Real.rpow_le_rpow_of_exponent_le hxone this`.

Take `⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩` from `nodeGap_poly hxb hY (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r) (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m)) (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0 (hnf.trans hf') h …`. Use `⟨?_, a2, a3, a5, a6, a7, a9⟩` and prove the remaining obligations. Establish `hb : 0 < L.sc.b` using `by unfold Scale.b; positivity`. Use `le_trans (le_of_eq ?_) a1` and prove the remaining obligations. Unfold `szlStar`.

Rewrite using `[div_div_eq_mul_div]`. Clear the denominators using the available nonvanishing facts.
-/
theorem szRow_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m := by
    have : D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m := by
      unfold Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m := by
    have e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ) := by
      rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)
  have hth : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : szTh L ≤ 1 := by unfold szTh; rw [hε]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hxone this
  obtain ⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩ := nodeGap_poly hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m))
    (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hth hth hH
  refine ⟨?_, a2, a3, a5, a6, a7, a9⟩
  have hb : 0 < L.sc.b := by unfold Scale.b; positivity
  refine le_trans (le_of_eq ?_) a1
  unfold szlStar
  rw [div_div_eq_mul_div]
  field_simp

end GlobalTheory.EX
