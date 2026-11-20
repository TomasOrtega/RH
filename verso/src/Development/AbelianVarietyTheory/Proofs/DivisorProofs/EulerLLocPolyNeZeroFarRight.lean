import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a m ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Complex.exp_add, ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))]`. Use `congr 1`.

Establish `hne : (1 - a * x) ≠ 0`. Introduce `h0`. Establish `ha` using `h a (Multiset.mem_cons_self a m)`. Establish `h1 : a * x = 1` using `by linear_combination -h0`. Rewrite `ha` using `[h1, norm_one]`.

Evaluate the numerical expressions using `at ha`. Rewrite using `[Complex.exp_neg, Complex.exp_log hne]`.
-/
lemma prod_inv_one_sub_eq_exp (x : ℂ) (m : Multiset ℂ) (h : ∀ b ∈ m, ‖b * x‖ ≤ 1 / 2) :
    (m.map fun b => (1 - b * x)⁻¹).prod =
      Complex.exp ((m.map fun b => -Complex.log (1 - b * x)).sum) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Complex.exp_add,
      ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))]
    congr 1
    have hne : (1 - a * x) ≠ 0 := by
      intro h0
      have ha := h a (Multiset.mem_cons_self a m)
      have h1 : a * x = 1 := by linear_combination -h0
      rw [h1, norm_one] at ha
      norm_num at ha
    rw [Complex.exp_neg, Complex.exp_log hne]

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a m ih`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]`. Establish `ha` using `h a (Multiset.mem_cons_self a m)`.

Establish `h1 : ‖-Complex.log (1 - a * x)‖ ≤ 3 / 2 * r`. Rewrite using `[norm_neg, sub_eq_add_neg]`. Use `(Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; linarith)).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2` using `ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_sum_neg_log_le (x : ℂ) (r : ℝ) (hr : r ≤ 1 / 2) (m : Multiset ℂ) (h : ∀ b ∈ m, ‖b * x‖ ≤ r) :
    ‖(m.map fun b => -Complex.log (1 - b * x)).sum‖ ≤ m.card * (3 / 2 * r) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a m)
    have h1 : ‖-Complex.log (1 - a * x)‖ ≤ 3 / 2 * r := by
      rw [norm_neg, sub_eq_add_neg]
      refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; linarith)).trans ?_
      rw [norm_neg]; linarith
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    calc _ ≤ ‖-Complex.log (1 - a * x)‖ + ‖(m.map fun b => -Complex.log (1 - b * x)).sum‖ :=
          norm_add_le _ _
      _ ≤ 3 / 2 * r + m.card * (3 / 2 * r) := add_le_add h1 h2
      _ = _ := by push_cast; ring

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `v.isPrime.ne_top`. Establish `: 2 ≤ Ideal.absNorm v.asIdeal` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
lemma two_le_absNorm_prime {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

/- English proof (translation)
Introduce `K _ _ n S B c hcard hB s hs`. Use `set t := s.re - c with ht`. Establish `ht2 : 2 < t` using `by rw [ht]; linarith`. Establish `key : ∀ w ∉ S, ∀ b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w), ‖b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (-t)`. Introduce `w hw b hb`.

Take `⟨b', hb', rfl⟩` from `Multiset.mem_map.mp hb`. Establish `hN2` using `two_le_absNorm_prime w`. Establish `hNpos : (0 : ℝ) < Ideal.absNorm w.asIdeal` using `by linarith`. Establish `hNpos' : 0 < Ideal.absNorm w.asIdeal` using `by exact_mod_cast hNpos`. Rewrite using `[norm_mul, Complex.norm_natCast_cpow_of_pos hNpos', Complex.neg_re]`.

Combine the equalities or inequalities in the displayed calculation. Establish `small : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) ≤ 1 / 2`. Introduce `w`. Establish `hN2` using `two_le_absNorm_prime w`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `set g : {w // w ∉ S} → ℂ := fun w => ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b => -Complex.log (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))).sum with hg`. Establish `hsumN : Summable fun w : {w // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t)` using `(GlobalTheory.summable_absNorm_rpow_heightOneSpectrum K t (by linarith)).subtype _`. Establish `hsum : Summable g`. Use `Summable.of_norm_bounded (g := fun w : {w // w ∉ S} => (n : ℝ) * (3 / 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t))) ?_ ?_` and prove the remaining obligations.

Conclude with `(hsumN.mul_left (3 / 2)).mul_left (n : ℝ)`. Introduce `w`. Establish `h` using `norm_sum_neg_log_le (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s)) ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t)) (small w.1) (Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)) (key w.1 w.2)`. Rewrite `h` using `[Multiset.card_map, hcard w.1 w.2]`. Conclude with `h`.

Establish `hprod : HasProd (fun w : {w // w ∉ S} => ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) (Complex.exp (∑' w, g w))`. Establish `h` using `hsum.hasSum.cexp`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using `only [Function.comp_apply, hg]`.

Conclude with `prod_inv_one_sub_eq_exp _ _ (fun b hb => (key w.1 w.2 b hb).trans (small w.1))`. Establish `hm : (fun w => ((B w).map fun b => (b : ℂ))) = fun w => Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w)`. Use function extensionality and compare the values at `fun w => by simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_id']`. Rewrite using `[hm]`. Unfold `eulerL`.

Rewrite using `[hprod.tprod_eq]`. Conclude with `Complex.exp_ne_zero _`. Introduce `w hw`. Rewrite using `[locPoly, Polynomial.eval_multiset_prod, Multiset.map_map]`. Use `Multiset.prod_ne_zero ?_` and prove the remaining obligations.

Introduce `h0`. Take `⟨b, hb, hb0⟩` from `Multiset.mem_map.mp h0`. Simplify using `only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X] at hb0`. Establish `hb' : b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w)`. Simplify `hb` using `only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton]`.

Establish `hk` using `(key w hw b hb').trans (small w)`. Establish `h1 : (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) = 1`. Take the linear combination `-hb0`. Rewrite `hk` using `[h1, norm_one]`. Evaluate the numerical expressions using `at hk`.
-/
theorem eulerL_locPoly_ne_zero_far_right : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ) (c : ℝ),
    (∀ w ∉ S, (B w).card = n) → (∀ w ∉ S, ∀ b ∈ B w, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c) →
    ∀ s : ℂ, c + 2 < s.re → eulerL K (fun w => (B w).map fun b => (b : ℂ)) S s ≠ 0 ∧
      ∀ w ∉ S, (locPoly (B w)).eval ((Ideal.absNorm w.asIdeal : ℂ) ^ (-s)) ≠ 0 := by
  intro K _ _ n S B c hcard hB s hs
  set t := s.re - c with ht
  have ht2 : 2 < t := by rw [ht]; linarith

  have key : ∀ w ∉ S, ∀ b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w),
      ‖b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hb
    have hN2 := two_le_absNorm_prime w
    have hNpos : (0 : ℝ) < Ideal.absNorm w.asIdeal := by linarith
    have hNpos' : 0 < Ideal.absNorm w.asIdeal := by exact_mod_cast hNpos
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos', Complex.neg_re]
    calc ‖(b' : ℂ)‖ * (Ideal.absNorm w.asIdeal : ℝ) ^ (-s.re)
        ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c * (Ideal.absNorm w.asIdeal : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hB w hw b' hb') (by positivity)
      _ = _ := by rw [← Real.rpow_add hNpos, ht]; ring_nf
  have small : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) ≤ 1 / 2 := by
    intro w
    have hN2 := two_le_absNorm_prime w
    calc (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
  refine ⟨?_, ?_⟩
  · set g : {w // w ∉ S} → ℂ := fun w =>
      ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b =>
        -Complex.log (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))).sum with hg
    have hsumN : Summable fun w : {w // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum K t (by linarith)).subtype _
    have hsum : Summable g := by
      refine Summable.of_norm_bounded (g := fun w : {w // w ∉ S} =>
        (n : ℝ) * (3 / 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t))) ?_ ?_
      · exact (hsumN.mul_left (3 / 2)).mul_left (n : ℝ)
      · intro w
        have h := norm_sum_neg_log_le (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-t)) (small w.1) (Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1))
          (key w.1 w.2)
        rw [Multiset.card_map, hcard w.1 w.2] at h
        exact h
    have hprod : HasProd (fun w : {w // w ∉ S} =>
        ((Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w.1)).map fun b =>
          (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) (Complex.exp (∑' w, g w)) := by
      have h := hsum.hasSum.cexp
      convert h using 1
      funext w
      simp only [Function.comp_apply, hg]
      exact prod_inv_one_sub_eq_exp _ _ (fun b hb => (key w.1 w.2 b hb).trans (small w.1))
    have hm : (fun w => ((B w).map fun b => (b : ℂ))) = fun w => Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w) :=
      funext fun w => by simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_id']
    rw [hm]
    unfold eulerL
    rw [hprod.tprod_eq]
    exact Complex.exp_ne_zero _
  · intro w hw
    rw [locPoly, Polynomial.eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero ?_
    intro h0
    obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X] at hb0
    have hb' : b ∈ Multiset.map (fun b : ℂˣ => (b : ℂ)) (B w) := by
      simpa only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton] using hb
    have hk := (key w hw b hb').trans (small w)
    have h1 : (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) = 1 := by
      linear_combination -hb0
    rw [h1, norm_one] at hk
    norm_num at hk

end GlobalTheory.HenQ
