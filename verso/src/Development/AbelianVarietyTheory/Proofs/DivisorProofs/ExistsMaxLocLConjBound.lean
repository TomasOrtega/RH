import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

open Complex ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.LogPos

/- English proof (translation)
Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a S ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, exp_add, ih fun w hw => h w (Multiset.mem_cons_of_mem hw)]`. Use `congr 1`.

Establish `ha : 1 - a ≠ 0`. Introduce `h0`. Establish `e : a = 1` using `by linear_combination -h0`. Use `h a (Multiset.mem_cons_self a S)` as an intermediate fact. Simplify using `[e] at this`.

Rewrite using `[exp_neg, exp_log ha]`.
-/
theorem prod_inv_one_sub_eq_exp (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    (S.map fun w => (1 - w)⁻¹).prod = exp (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, exp_add,
      ih fun w hw => h w (Multiset.mem_cons_of_mem hw)]
    congr 1
    have ha : 1 - a ≠ 0 := by
      intro h0
      have e : a = 1 := by linear_combination -h0
      have := h a (Multiset.mem_cons_self a S)
      simp [e] at this
    rw [exp_neg, exp_log ha]

/- English proof (translation)
Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simpa using hasSum_zero`. Consider the case `cons a S ih`. Simplify using `only [Multiset.map_cons, Multiset.sum_cons, add_div]`. Conclude with `(hasSum_taylorSeries_neg_log (h a (Multiset.mem_cons_self a S))).add (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))`.
-/
theorem hasSum_log (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    HasSum (fun n : ℕ => (S.map fun w => w ^ n).sum / n) (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasSum_zero
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
    exact (hasSum_taylorSeries_neg_log (h a (Multiset.mem_cons_self a S))).add
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map]`. Simplify using `only [Function.comp_def, mul_pow]`.

Rewrite using `[Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Multiset.map_cons, Multiset.sum_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_pow_product (x : ℂ) (n : ℕ) (s t : Multiset ℂˣ) :
    ((s ×ˢ t).map fun p : ℂˣ × ℂˣ => ((p.1 : ℂ) * p.2 * x) ^ n).sum =
      x ^ n * (s.map fun b : ℂˣ => (b : ℂ) ^ n).sum * (t.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map]
    simp only [Function.comp_def, mul_pow]
    rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Multiset.map_cons, Multiset.sum_cons]
    ring

/- English proof (translation)
Rewrite using `[map_multiset_sum, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[Units.coe_star, star_pow]`.
-/
theorem sum_pow_star (n : ℕ) (B : Multiset ℂˣ) :
    ((B.map star).map fun b : ℂˣ => (b : ℂ) ^ n).sum = conj (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp [Units.coe_star, star_pow]

/- English proof (translation)
Rewrite using `[ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]`.
-/
theorem cpow_neg_eq (q : ℕ) (σ : ℝ) : (q : ℂ) ^ (-(σ : ℂ)) = (((q : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]

/- English proof (translation)
Rewrite `hp` using `[Multiset.mem_product]`. Take `⟨b', hb', hpb⟩` from `Multiset.mem_map.1 hp.2`. Establish `h1` using `hM _ hp.1`. Establish `h2` using `hM _ hb'`. Establish `e2 : ‖(p.2 : ℂ)‖ = ‖(b' : ℂ)‖` using `by rw [← hpb, Units.coe_star, norm_star]`.

Rewrite using `[e2]`. Use polynomial arithmetic with `[sq_nonneg (‖(p.1 : ℂ)‖ - ‖(b' : ℂ)‖)]`.
-/
theorem norm_pair_le {B : Multiset ℂˣ} {M : ℝ} (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) {p : ℂˣ × ℂˣ}
    (hp : p ∈ B ×ˢ B.map star) : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ M := by
  rw [Multiset.mem_product] at hp
  obtain ⟨b', hb', hpb⟩ := Multiset.mem_map.1 hp.2
  have h1 := hM _ hp.1
  have h2 := hM _ hb'
  have e2 : ‖(p.2 : ℂ)‖ = ‖(b' : ℂ)‖ := by rw [← hpb, Units.coe_star, norm_star]
  rw [e2]
  nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(b' : ℂ)‖)]

/- English proof (translation)
Use `set x : ℝ := (q : ℝ) ^ (-σ) with hxdef`. Establish `hx0 : 0 ≤ x` using `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Use `set S := (B ×ˢ B.map star).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * x with hSdef`. Establish `hS : ∀ w ∈ S, ‖w‖ < 1`. Introduce `w hw`.

Take `⟨p, hp, rfl⟩` from `Multiset.mem_map.1 hw`. Use `norm_pair_le hM hp` as an intermediate fact. Rewrite using `[norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hx0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right this hx0]`. Establish `hloc : locL q B (B.map star) σ = (S.map fun w => (1 - w)⁻¹).prod`.

Simplify using `only [locL, cpow_neg_eq, ← hxdef, hSdef, Multiset.map_map, Function.comp_def]`. Establish `hterm : ∀ n : ℕ, (S.map fun w => w ^ n).sum / n = ((x ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n : ℝ) : ℂ)`. Introduce `n`. Simplify using `only [hSdef, Multiset.map_map, Function.comp_def]`. Rewrite using `[sum_pow_product, sum_pow_star, mul_assoc, mul_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hL` using `hasSum_log S hS`. Simplify using `only [hterm] at hL`. Establish `hre` using `Complex.hasSum_re hL`.

Establish `him` using `Complex.hasSum_im hL`. Simplify using `only [ofReal_re, ofReal_im] at hre him`. Establish `hLim` using `him.unique hasSum_zero`. Use `⟨_, hre, ?_⟩` and prove the remaining obligations. Rewrite using `[hloc, prod_inv_one_sub_eq_exp S hS, ofReal_exp]`.

Use `congr 1`. Conclude with `Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, hLim])`.
-/
theorem locL_conj_eq_exp (q : ℕ) (B : Multiset ℂˣ) (M : ℝ) (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) (σ : ℝ)
    (hσ : M * (q : ℝ) ^ (-σ) < 1) :
    ∃ L : ℝ, HasSum (fun n : ℕ => ((q : ℝ) ^ (-σ)) ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n) L ∧
      locL q B (B.map star) σ = Real.exp L := by
  set x : ℝ := (q : ℝ) ^ (-σ) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set S := (B ×ˢ B.map star).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * x with hSdef
  have hS : ∀ w ∈ S, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hw
    have := norm_pair_le hM hp
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hx0]
    nlinarith [mul_le_mul_of_nonneg_right this hx0]
  have hloc : locL q B (B.map star) σ = (S.map fun w => (1 - w)⁻¹).prod := by
    simp only [locL, cpow_neg_eq, ← hxdef, hSdef, Multiset.map_map, Function.comp_def]
  have hterm : ∀ n : ℕ, (S.map fun w => w ^ n).sum / n =
      ((x ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n : ℝ) : ℂ) := by
    intro n
    simp only [hSdef, Multiset.map_map, Function.comp_def]
    rw [sum_pow_product, sum_pow_star, mul_assoc, mul_conj]
    push_cast
    ring
  have hL := hasSum_log S hS
  simp only [hterm] at hL
  have hre := Complex.hasSum_re hL
  have him := Complex.hasSum_im hL
  simp only [ofReal_re, ofReal_im] at hre him
  have hLim := him.unique hasSum_zero
  refine ⟨_, hre, ?_⟩
  rw [hloc, prod_inv_one_sub_eq_exp S hS, ofReal_exp]
  congr 1
  exact Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, hLim])

end GlobalTheory.JSW.LogPos
