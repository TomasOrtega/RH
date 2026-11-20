import Mathlib
import Formalism.GL3MeanSquares.WeightedSumIntegralFormula
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.ZetaNonvanishing.ZetaRealNonvanish

namespace Formalism.HermitianLattices.GL2b2
namespace PfN

section A
open Complex

/- English proof (translation)
Establish `hder : ∀ t ∈ Set.Icc x y, HasDerivWithinAt (fun u : ℝ => ((u : ℝ) : ℂ) ^ (-s)) ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) (Set.Icc x y) t`. Introduce `t ht`. Establish `ht0 : 0 < t` using `lt_of_lt_of_le hx ht.1`. Establish `h1 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) ((t : ℝ) : ℂ)`. Use `(hasDerivAt_id ((t : ℝ) : ℂ)).cpow_const (c := -s) (Complex.ofReal_mem_slitPlane.2 ht0)` as an intermediate fact.

Simplify using `using this`. Conclude with `h1.comp_ofReal.hasDerivWithinAt`. Establish `hb : ∀ t ∈ Set.Icc x y, ‖(-s) * ((t : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1)`. Introduce `t ht`. Establish `ht0 : 0 < t` using `lt_of_lt_of_le hx ht.1`.

Rewrite using `[norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]`. Apply `mul_le_mul_of_nonneg_left _ (norm_nonneg _)` to reduce the goal to its premises. Establish `: (-s - 1).re = -s.re - 1` using `by simp`. Rewrite using `[this]`. Conclude with `Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 ht0) ht.1`.

Use `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc x y) (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy)` as an intermediate fact. Rewrite `this` using `[Real.norm_of_nonneg (by linarith)]`. Then use the resulting hypothesis.
-/
theorem cpow_diff_bound (s : ℂ) (hs : 0 ≤ s.re) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖((y : ℝ) : ℂ) ^ (-s) - ((x : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) * (y - x) := by
  have hder : ∀ t ∈ Set.Icc x y, HasDerivWithinAt (fun u : ℝ => ((u : ℝ) : ℂ) ^ (-s))
      ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) (Set.Icc x y) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    have h1 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) ((t : ℝ) : ℂ) := by
      have := (hasDerivAt_id ((t : ℝ) : ℂ)).cpow_const (c := -s) (Complex.ofReal_mem_slitPlane.2 ht0)
      simpa using this
    exact h1.comp_ofReal.hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc x y, ‖(-s) * ((t : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have : (-s - 1).re = -s.re - 1 := by simp
    rw [this]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 ht0) ht.1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc x y)
    (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy)
  rwa [Real.norm_of_nonneg (by linarith)] at this

noncomputable def tt (k : ℕ) (s : ℂ) : ℂ :=
  ((8 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 3 : ℝ) : ℂ) ^ (-s) -
    ((8 * (k : ℝ) + 5 : ℝ) : ℂ) ^ (-s) + ((8 * (k : ℝ) + 7 : ℝ) : ℂ) ^ (-s)

noncomputable def tr (k : ℕ) (σ : ℝ) : ℝ :=
  (8 * (k : ℝ) + 1) ^ (-σ) - (8 * (k : ℝ) + 3) ^ (-σ) - (8 * (k : ℝ) + 5) ^ (-σ) +
    (8 * (k : ℝ) + 7) ^ (-σ)

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `aux : ∀ c : ℝ, 1 ≤ c → (8 * (k : ℝ) + c) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-1 - δ)`. Introduce `c hc`. Combine the equalities or inequalities in the displayed calculation. Establish `b1` using `cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 1) (8 * (k : ℝ) + 3) (by linarith) (by linarith)`.

Establish `b2` using `cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 5) (8 * (k : ℝ) + 7) (by linarith) (by linarith)`. Establish `hP : 0 ≤ ((k : ℝ) + 1) ^ (-1 - δ)` using `Real.rpow_nonneg (by linarith) _`. Establish `hR : 0 ≤ R` using `le_trans (norm_nonneg _) h2`. Establish `c1 : ‖s‖ * (8 * (k : ℝ) + 1) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ)` using `mul_le_mul h2 (aux 1 le_rfl) (Real.rpow_nonneg (by linarith) _) hR`. Establish `c2 : ‖s‖ * (8 * (k : ℝ) + 5) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ)` using `mul_le_mul h2 (aux 5 (by norm_num)) (Real.rpow_nonneg (by linarith) _) hR`.

Establish `e : tt k s = -(((8 * (k : ℝ) + 3 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) + (((8 * (k : ℝ) + 7 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 5 : ℝ) : ℂ) ^ (-s))`. Unfold `tt`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Establish `d1 : (8 * (k : ℝ) + 3) - (8 * (k : ℝ) + 1) = 2` using `by ring`. Establish `d2 : (8 * (k : ℝ) + 7) - (8 * (k : ℝ) + 5) = 2` using `by ring`. Rewrite `b1` using `[d1]`. Rewrite `b2` using `[d2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tt_bound (k : ℕ) (s : ℂ) (δ R : ℝ) (hδ : 0 < δ) (h1 : δ ≤ s.re) (h2 : ‖s‖ ≤ R) :
    ‖tt k s‖ ≤ 4 * R * ((k : ℝ) + 1) ^ (-1 - δ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → (8 * (k : ℝ) + c) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-1 - δ) := by
    intro c hc
    calc (8 * (k : ℝ) + c) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) :=
          Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 (by linarith))
            (Set.mem_Ioi.2 (by linarith)) (by linarith)
      _ ≤ ((k : ℝ) + 1) ^ (-1 - δ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have b1 := cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 1) (8 * (k : ℝ) + 3) (by linarith) (by linarith)
  have b2 := cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 5) (8 * (k : ℝ) + 7) (by linarith) (by linarith)
  have hP : 0 ≤ ((k : ℝ) + 1) ^ (-1 - δ) := Real.rpow_nonneg (by linarith) _
  have hR : 0 ≤ R := le_trans (norm_nonneg _) h2
  have c1 : ‖s‖ * (8 * (k : ℝ) + 1) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ) :=
    mul_le_mul h2 (aux 1 le_rfl) (Real.rpow_nonneg (by linarith) _) hR
  have c2 : ‖s‖ * (8 * (k : ℝ) + 5) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ) :=
    mul_le_mul h2 (aux 5 (by norm_num)) (Real.rpow_nonneg (by linarith) _) hR
  have e : tt k s = -(((8 * (k : ℝ) + 3 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) +
      (((8 * (k : ℝ) + 7 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 5 : ℝ) : ℂ) ^ (-s)) := by
    unfold tt; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have d1 : (8 * (k : ℝ) + 3) - (8 * (k : ℝ) + 1) = 2 := by ring
  have d2 : (8 * (k : ℝ) + 7) - (8 * (k : ℝ) + 5) = 2 := by ring
  rw [d1] at b1
  rw [d2] at b2
  linarith

/- English proof (translation)
Apply `Summable.mul_left` to reduce the goal to its premises. Establish `h` using `(summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -1 - δ < -1 by linarith))`. Simplify using `using h`.
-/
theorem summable_u (δ R : ℝ) (hδ : 0 < δ) :
    Summable (fun k : ℕ => 4 * R * ((k : ℝ) + 1) ^ (-1 - δ)) := by
  apply Summable.mul_left
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -1 - δ < -1 by linarith))
  simpa using h

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `aux : ∀ c : ℝ, 1 ≤ c → Differentiable ℂ (fun s : ℂ => ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-s))`. Introduce `c hc`. Apply `Differentiable.const_cpow differentiable_id.neg` to reduce the goal to its premises. Use `left`.

Establish `: (8 * (k : ℝ) + c) ≠ 0` using `by positivity`. Conclude with `this` after adjusting the coercions. Unfold `tt`. Conclude with `(((aux 1 le_rfl).sub (aux 3 (by norm_num))).sub (aux 5 (by norm_num))).add (aux 7 (by norm_num))`.
-/
theorem tt_differentiable (k : ℕ) : Differentiable ℂ (tt k) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → Differentiable ℂ (fun s : ℂ => ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-s)) := by
    intro c hc
    apply Differentiable.const_cpow differentiable_id.neg
    left
    have : (8 * (k : ℝ) + c) ≠ 0 := by positivity
    exact_mod_cast this
  unfold tt
  exact (((aux 1 le_rfl).sub (aux 3 (by norm_num))).sub (aux 5 (by norm_num))).add (aux 7 (by norm_num))

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `aux : ∀ c : ℝ, 1 ≤ c → ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-(σ : ℂ)) = (((8 * (k : ℝ) + c) ^ (-σ) : ℝ) : ℂ)`. Introduce `c hc`. Rewrite using `[ofReal_cpow (by positivity), ofReal_neg]`. Unfold `tt tr`.

Rewrite using `[aux 1 le_rfl, aux 3 (by norm_num), aux 5 (by norm_num), aux 7 (by norm_num)]`. Simplify using `only [ofReal_add, ofReal_sub]`.
-/
theorem tt_ofReal (k : ℕ) (σ : ℝ) : tt k (σ : ℂ) = ((tr k σ : ℝ) : ℂ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → ((8 * (k : ℝ) + c : ℝ) : ℂ) ^ (-(σ : ℂ)) = (((8 * (k : ℝ) + c) ^ (-σ) : ℝ) : ℂ) := by
    intro c hc
    rw [ofReal_cpow (by positivity), ofReal_neg]
  unfold tt tr
  rw [aux 1 le_rfl, aux 3 (by norm_num), aux 5 (by norm_num), aux 7 (by norm_num)]
  simp only [ofReal_add, ofReal_sub]

/- English proof (translation)
Establish `hx' : 0 < x'` using `hx.trans hxx`. Establish `f : ∀ y : ℝ, 0 < y → (y + 2) ^ (-σ) = y ^ (-σ) * (1 + 2 / y) ^ (-σ)`. Introduce `y hy`. Rewrite using `[← Real.mul_rpow hy.le (by positivity)]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[f x hx, f x' hx']`. Establish `hA : x' ^ (-σ) < x ^ (-σ)` using `Real.rpow_lt_rpow_of_neg hx hxx (by linarith)`. Establish `hA' : 0 < x' ^ (-σ)` using `Real.rpow_pos_of_pos hx' _`. Establish `h2 : 2 / x' < 2 / x` using `div_lt_div_of_pos_left (by norm_num) hx hxx`.

Establish `hB : (1 + 2 / x) ^ (-σ) < (1 + 2 / x') ^ (-σ)` using `Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)`. Establish `hB' : (1 + 2 / x') ^ (-σ) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by have : 0 < 2 / x' := by positivity linarith) (by linarith)`. Use polynomial arithmetic with `[mul_pos hA' (sub_pos.2 hB'), mul_pos (sub_pos.2 hA) (sub_pos.2 (hB.trans hB')), mul_pos hA' (sub_pos.2 hB)]`.
-/
theorem hdecr (σ x x' : ℝ) (hσ : 0 < σ) (hx : 0 < x) (hxx : x < x') :
    x' ^ (-σ) - (x' + 2) ^ (-σ) < x ^ (-σ) - (x + 2) ^ (-σ) := by
  have hx' : 0 < x' := hx.trans hxx
  have f : ∀ y : ℝ, 0 < y → (y + 2) ^ (-σ) = y ^ (-σ) * (1 + 2 / y) ^ (-σ) := by
    intro y hy
    rw [← Real.mul_rpow hy.le (by positivity)]
    congr 1
    field_simp
  rw [f x hx, f x' hx']
  have hA : x' ^ (-σ) < x ^ (-σ) := Real.rpow_lt_rpow_of_neg hx hxx (by linarith)
  have hA' : 0 < x' ^ (-σ) := Real.rpow_pos_of_pos hx' _
  have h2 : 2 / x' < 2 / x := div_lt_div_of_pos_left (by norm_num) hx hxx
  have hB : (1 + 2 / x) ^ (-σ) < (1 + 2 / x') ^ (-σ) :=
    Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  have hB' : (1 + 2 / x') ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by have : 0 < 2 / x' := by positivity
                                          linarith) (by linarith)
  nlinarith [mul_pos hA' (sub_pos.2 hB'), mul_pos (sub_pos.2 hA) (sub_pos.2 (hB.trans hB')),
    mul_pos hA' (sub_pos.2 hB)]

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Use `hdecr σ (8 * (k : ℝ) + 1) (8 * (k : ℝ) + 5) hσ (by linarith) (by linarith)` as an intermediate fact. Establish `e1 : 8 * (k : ℝ) + 1 + 2 = 8 * (k : ℝ) + 3` using `by ring`. Establish `e2 : 8 * (k : ℝ) + 5 + 2 = 8 * (k : ℝ) + 7` using `by ring`. Rewrite `this` using `[e1, e2]`.

Unfold `tr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tr_pos (k : ℕ) (σ : ℝ) (hσ : 0 < σ) : 0 < tr k σ := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have := hdecr σ (8 * (k : ℝ) + 1) (8 * (k : ℝ) + 5) hσ (by linarith) (by linarith)
  have e1 : 8 * (k : ℝ) + 1 + 2 = 8 * (k : ℝ) + 3 := by ring
  have e2 : 8 * (k : ℝ) + 5 + 2 = 8 * (k : ℝ) + 7 := by ring
  rw [e1, e2] at this
  unfold tr
  linarith

/- English proof (translation)
Establish `: ((k * 8 + j : ℕ) : ZMod 8) = (j : ZMod 8)`. Use `push_cast`. Establish `h8 : (8 : ZMod 8) = 0` using `by decide`. Rewrite using `[h8]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem chi8_value_shift (k j : ℕ) : ZeroFreeRegionGL2.chi8 ((k * 8 + j : ℕ) : ZMod 8) = ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) := by
  have : ((k * 8 + j : ℕ) : ZMod 8) = (j : ZMod 8) := by
    push_cast
    have h8 : (8 : ZMod 8) = 0 := by decide
    rw [h8]; ring
  rw [this]
  rfl

/- English proof (translation)
Rewrite using `[DirichletCharacter.LFunction_eq_LSeries _ hs]`. Establish `hsum` using `DirichletCharacter.LSeriesSummable_of_one_lt_re ZeroFreeRegionGL2.chi8 hs`. Unfold `LSeriesSummable at hsum`. Unfold `LSeries`. Rewrite using `[← (Nat.divModEquiv 8).symm.tsum_eq]`.

Establish `hsum'` using `(Nat.divModEquiv 8).symm.summable_iff.2 hsum`. Establish `h3 : ∑' c : ℕ × Fin 8, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s ((Nat.divModEquiv 8).symm c) = ∑' k : ℕ, ∑' j : Fin 8, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s ((Nat.divModEquiv 8).symm (k, j))` using `hsum'.tsum_prod`. Rewrite using `[h3]`. Use `congr 1`. Use extensionality with `k`.

Rewrite using `[tsum_fintype, Fin.sum_univ_eight]`. Establish `hf0 : (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) 0 = 0`. Use `chi8_value_shift 0 0` as an intermediate fact. Simplify using `only [zero_mul, add_zero] at this`. Use `show ZeroFreeRegionGL2.chi8 ((0 : ℕ) : ZMod 8) = 0`.

Rewrite using `[this]`. Establish `: ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0` using `by decide`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hterm : ∀ j : ℕ, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + j) = ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) * ((8 * (k : ℝ) + (j : ℝ) : ℝ) : ℂ) ^ (-s)`.

Introduce `j`. Rewrite using `[LSeries.term_def₀ hf0, chi8_value_shift]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 0) + LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 1) + LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 2) + LSeries.term (fun n : ℕ => ZeroFree …`. Rewrite using `[hterm 0, hterm 1, hterm 2, hterm 3, hterm 4, hterm 5, hterm 6, hterm 7]`. Establish `v0 : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0` using `by decide`. Establish `v1 : ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1` using `by decide`. Establish `v2 : ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0` using `by decide`.

Establish `v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1` using `by decide`. Establish `v4 : ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0` using `by decide`. Establish `v5 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1` using `by decide`. Establish `v6 : ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0` using `by decide`. Establish `v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1` using `by decide`.

Rewrite using `[v0, v1, v2, v3, v4, v5, v6, v7]`. Unfold `tt`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem series_eq (s : ℂ) (hs : 1 < s.re) :
    DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 s = ∑' k, tt k s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re ZeroFreeRegionGL2.chi8 hs
  unfold LSeriesSummable at hsum
  unfold LSeries
  rw [← (Nat.divModEquiv 8).symm.tsum_eq]
  have hsum' := (Nat.divModEquiv 8).symm.summable_iff.2 hsum
  have h3 : ∑' c : ℕ × Fin 8, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s
      ((Nat.divModEquiv 8).symm c) = ∑' k : ℕ, ∑' j : Fin 8,
        LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s ((Nat.divModEquiv 8).symm (k, j)) :=
    hsum'.tsum_prod
  rw [h3]
  congr 1
  ext k
  rw [tsum_fintype, Fin.sum_univ_eight]
  have hf0 : (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) 0 = 0 := by
    have := chi8_value_shift 0 0
    simp only [zero_mul, add_zero] at this
    show ZeroFreeRegionGL2.chi8 ((0 : ℕ) : ZMod 8) = 0
    rw [this]
    have : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 := by decide
    rw [this]; simp
  have hterm : ∀ j : ℕ, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + j) =
      ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) * ((8 * (k : ℝ) + (j : ℝ) : ℝ) : ℂ) ^ (-s) := by
    intro j
    rw [LSeries.term_def₀ hf0, chi8_value_shift]
    congr 2
    push_cast; ring
  show LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 0) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 1) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 2) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 3) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 4) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 5) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 6) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 7) = tt k s
  rw [hterm 0, hterm 1, hterm 2, hterm 3, hterm 4, hterm 5, hterm 6, hterm 7]
  have v0 : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 := by decide
  have v1 : ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 := by decide
  have v2 : ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 := by decide
  have v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
  have v4 : ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 := by decide
  have v5 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
  have v6 : ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 := by decide
  have v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
  rw [v0, v1, v2, v3, v4, v5, v6, v7]
  unfold tt
  push_cast
  ring

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (fun χ : DirichletCharacter ℂ 8 => χ (3 : ZMod 8)) h`. Establish `h3 : IsUnit (3 : ZMod 8)` using `by decide`. Simplify using `only [MulChar.one_apply h3] at h1`. Establish `h2 : ZeroFreeRegionGL2.chi8 (3 : ZMod 8) = -1`.

Unfold `ZeroFreeRegionGL2.chi8`. Simplify using `only [MulChar.ringHomComp_apply]`. Establish `: ZMod.χ₈ 3 = -1` using `by decide`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[h2]`. Evaluate the numerical expressions using `at h1`.
-/
theorem chi_eight_ne_one : ZeroFreeRegionGL2.chi8 ≠ 1 := by
  intro h
  have h1 := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (3 : ZMod 8)) h
  have h3 : IsUnit (3 : ZMod 8) := by decide
  simp only [MulChar.one_apply h3] at h1
  have h2 : ZeroFreeRegionGL2.chi8 (3 : ZMod 8) = -1 := by
    unfold ZeroFreeRegionGL2.chi8
    simp only [MulChar.ringHomComp_apply]
    have : ZMod.χ₈ 3 = -1 := by decide
    rw [this]; simp
  rw [h2] at h1
  norm_num at h1

/- English proof (translation)
Set `U : Set ℂ` to `{s | σ / 2 < s.re} ∩ Metric.ball 0 3`. Establish `hUo : IsOpen U` using `(isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball`. Establish `hUc : Convex ℝ U` using `(convex_halfSpace_re_gt _).inter (convex_ball _ _)`. Establish `hG : DifferentiableOn ℂ (fun s => ∑' k, tt k s) U`. Apply `differentiableOn_tsum_of_summable_norm (summable_u (σ / 2) 3 (by linarith)) (fun k => (tt_differentiable k).differentiableOn) hUo` to reduce the goal to its premises.

Introduce `k w hw`. Conclude with `tt_bound k w (σ / 2) 3 (by linarith) hw.1.le (mem_ball_zero_iff.1 hw.2).le`. Establish `hL : DifferentiableOn ℂ (DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8) U` using `(DirichletCharacter.differentiable_LFunction chi_eight_ne_one).differentiableOn`. Establish `h2U : (2 : ℂ) ∈ U` using `⟨by simp; linarith, by simp; norm_num⟩`. Establish `hσU : (σ : ℂ) ∈ U` using `⟨by simp; linarith, by simp [abs_of_pos h0]; linarith⟩`.

Establish `hev : DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 =ᶠ[nhds (2 : ℂ)] (fun s => ∑' k, tt k s)`. Establish `: {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ)` using `(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)`. Use `filter_upwards [this] with s hs using series_eq s hs`. Conclude with `(hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo) hUc.isPreconnected h2U hev hσU`.
-/
theorem L_eq (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) = ∑' k, tt k (σ : ℂ) := by
  let U : Set ℂ := {s | σ / 2 < s.re} ∩ Metric.ball 0 3
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have hG : DifferentiableOn ℂ (fun s => ∑' k, tt k s) U := by
    apply differentiableOn_tsum_of_summable_norm (summable_u (σ / 2) 3 (by linarith))
      (fun k => (tt_differentiable k).differentiableOn) hUo
    intro k w hw
    exact tt_bound k w (σ / 2) 3 (by linarith) hw.1.le (mem_ball_zero_iff.1 hw.2).le
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8) U :=
    (DirichletCharacter.differentiable_LFunction chi_eight_ne_one).differentiableOn
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, by simp; norm_num⟩
  have hσU : (σ : ℂ) ∈ U := ⟨by simp; linarith, by simp [abs_of_pos h0]; linarith⟩
  have hev : DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 =ᶠ[nhds (2 : ℂ)] (fun s => ∑' k, tt k s) := by
    have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs using series_eq s hs
  exact (hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo)
    hUc.isPreconnected h2U hev hσU

/- English proof (translation)
Use `⟨Formalism.zetaRealNonvanish, ?_⟩` and prove the remaining obligations. Introduce `σ h0 h1`. Rewrite using `[L_eq σ h0 h1]`. Repeatedly rewrite using `[tt_ofReal]`. Rewrite using `[← Complex.ofReal_tsum]`.

Establish `hs : Summable (fun k => tr k σ)`. Apply `Summable.of_norm_bounded (summable_u σ 1 h0)` to reduce the goal to its premises. Introduce `k`. Use `tt_bound k (σ : ℂ) σ 1 h0 (by simp) (by simp [abs_of_pos h0]; linarith)` as an intermediate fact. Rewrite `this` using `[tt_ofReal, Complex.norm_real]`. Then use the resulting hypothesis.

Use `hs.tsum_pos (fun k => (tr_pos k σ h0).le) 0 (tr_pos 0 σ h0)` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions.
-/
theorem noRealZeroSmall : NoRealZeroSmall := by
  refine ⟨Formalism.zetaRealNonvanish, ?_⟩
  intro σ h0 h1
  rw [L_eq σ h0 h1]
  simp_rw [tt_ofReal]
  rw [← Complex.ofReal_tsum]
  have hs : Summable (fun k => tr k σ) := by
    apply Summable.of_norm_bounded (summable_u σ 1 h0)
    intro k
    have := tt_bound k (σ : ℂ) σ 1 h0 (by simp) (by simp [abs_of_pos h0]; linarith)
    rwa [tt_ofReal, Complex.norm_real] at this
  have := hs.tsum_pos (fun k => (tr_pos k σ h0).le) 0 (tr_pos 0 σ h0)
  exact_mod_cast this.ne'

end A

section B
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.ZeroFreeRegionGL2

end B

end PfN

/- English proof (translation)
The claim follows from `PfN.noRealZeroSmall`.
-/
theorem no_real_zero_small_modulus : NoRealZeroSmall := PfN.noRealZeroSmall

end Formalism.HermitianLattices.GL2b2
