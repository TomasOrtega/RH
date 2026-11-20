import Mathlib
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

namespace Formalism.PairingDivisionLocalBalance

/- English proof (translation)
Unfold `Formalism.DivisionValues.lw`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`.
-/
theorem lw_nonneg {K : Type} [Field K] [NumberField K] (w : Pl K) : 0 ≤ lw w := by
  unfold Formalism.DivisionValues.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

/- English proof (translation)
Use `Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)` as an intermediate fact. Simplify using `using this`.
-/
theorem vw_natCast_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (n : ℕ) :
    0 ≤ vw w (n : K) := by
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  simpa using this

/- English proof (translation)
Introduce `K _ _ _ _ S c`. Establish `hs : ∀ l ∈ S, (Function.support fun w : Pl K => c l * (lw w * (vw w (l : K) : ℝ))).Finite`. Introduce `l _`. Use `(sum_valuation_nat K l).1.subset ?_` and prove the remaining obligations. Introduce `w hw`.

Simplify using `only [Function.mem_support] at hw ⊢`. Conclude with `right_ne_zero_of_mul hw`. Establish `he : (fun w : Pl K => lw w * wt S c w) = fun w => ∑ l ∈ S, c l * (lw w * (vw w (l : K) : ℝ))`. Use function extensionality and compare the values at `w`. Unfold `wt`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Use `(Set.Finite.biUnion S.finite_toSet hs).subset ?_` and prove the remaining obligations.

Introduce `w hw`. Simplify using `only [Function.mem_support] at hw`. Take `⟨l, hl, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hw`. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨l, hl, hne⟩`.

Rewrite using `[he, finsum_sum_comm _ _ hs]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_finsum, (sum_valuation_nat K l).2]`. Introduce `hc w`. Conclude with `Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) (by exact_mod_cast vw_natCast_nonneg w l)`.
-/
theorem weight_sum' : WtSum := by
  intro K _ _ _ _ S c
  have hs : ∀ l ∈ S, (Function.support fun w : Pl K => c l * (lw w * (vw w (l : K) : ℝ))).Finite := by
    intro l _
    refine (sum_valuation_nat K l).1.subset ?_
    intro w hw
    simp only [Function.mem_support] at hw ⊢
    exact right_ne_zero_of_mul hw
  have he : (fun w : Pl K => lw w * wt S c w) =
      fun w => ∑ l ∈ S, c l * (lw w * (vw w (l : K) : ℝ)) := by
    funext w; unfold wt; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    refine (Set.Finite.biUnion S.finite_toSet hs).subset ?_
    intro w hw
    simp only [Function.mem_support] at hw
    obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    simp only [Set.mem_iUnion]
    exact ⟨l, hl, hne⟩
  · rw [he, finsum_sum_comm _ _ hs]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_finsum, (sum_valuation_nat K l).2]
  · intro hc w
    exact Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) (by exact_mod_cast vw_natCast_nonneg w l)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero n ha) ha, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vw_pow {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = n * vw w a := by
  induction n with
  | zero => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | succ n ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero n ha) ha, ih]; push_cast; ring

/- English proof (translation)
Introduce `K _ _ _ _ a De M nff o vA S N0 ha hDe hD hlo hhi hN hL2`. Use `set β : K := a ^ 12 * (De ^ M)⁻¹ with hβ`. Establish `hβ0 : β ≠ 0` using `mul_ne_zero (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe))`. Establish `hvβ : ∀ w : Pl K, vw w β = 12 * (vw w a + M * o w)`. Introduce `w`.

Rewrite using `[hβ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe)), Formalism.DivisionValues.ValuationRepresentative.vw_inv, vw_pow w a ha, vw_pow w De hDe, hD w]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨pf1, pf2⟩` from `Formalism.DivisionValues.prod_formula' K β hβ0`. Take `⟨n1, n2⟩` from `sum_valuation_nat K nff`.

Take `⟨w1, w2, w3⟩` from `weight_sum' K S N0`. Establish `hfin : (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite`. Use `(pf1.union n1).subset ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Function.mem_support, Set.mem_union] at hw ⊢`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨c1, c2⟩` from `hcon`. Establish `hl : lw w ≠ 0` using `left_ne_zero_of_mul hw`. Establish `d1 : vw w β = 0`.

Use `(mul_eq_zero.mp c1).resolve_left hl` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `d2 : vw w (nff : K) = 0`. Use `(mul_eq_zero.mp c2).resolve_left hl` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `e1` using `hvβ w`. Establish `e2` using `hlo w`. Establish `e3` using `hhi w`. Rewrite `e3` using `[d2]`. Establish `: vA w = 0` using `by omega`.

Apply `hw` to reduce the goal to its premises. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hpt : ∀ w : Pl K, lw w * |(vA w : ℝ)| ≤ (1 / 12) * (lw w * (vw w β : ℝ)) + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ)) + 2 * (lw w * wt S N0 w)`.

Introduce `w`. Establish `h0` using `lw_nonneg w`. Establish `h1 : ((vw w β : ℤ) : ℝ) = 12 * ((vw w a : ℝ) + M * o w)` using `by rw [hvβ w]; push_cast; ring`. Establish `h2 : (vA w : ℝ) ≤ (vw w a : ℝ) + M * o w + M * vw w (nff : K)` using `by exact_mod_cast hhi w`. Establish `h3` using `hL2 w`.

Establish `h4` using `w3 hN w`. Establish `h5 : |(vA w : ℝ)| ≤ (vA w : ℝ) + 2 * wt S N0 w`. Apply the tactic sequence `rcases abs_cases (vA w : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith`. Establish `h6 : |(vA w : ℝ)| ≤ (1 / 12) * (vw w β : ℝ) + M * vw w (nff : K) + 2 * wt S N0 w`. Rewrite using `[h1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `s1 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))).Finite` using `pf1.subset fun w hw => right_ne_zero_of_mul hw`. Establish `s2 : (Function.support fun w : Pl K => (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite` using `n1.subset fun w hw => right_ne_zero_of_mul hw`. Establish `s3 : (Function.support fun w : Pl K => (2 : ℝ) * (lw w * wt S N0 w)).Finite` using `w1.subset fun w hw => right_ne_zero_of_mul hw`.

Establish `s12 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ)) + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite` using `(s1.union s2).subset (Function.support_add _ _)`. Establish `s123 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ)) + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ)) + 2 * (lw w * wt S N0 w)).Finite` using `(s12.union s3).subset (Function.support_add _ _)`. Use `(finsum_le_finsum' hfin s123 hpt).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[finsum_add_distrib s12 s3, finsum_add_distrib s1 s2, ← mul_finsum, ← mul_finsum, ← mul_finsum, ← pf2, n2, w2]`. Both sides reduce to the same expression.
-/
theorem height_bound_essential : HeightCore := by
  intro K _ _ _ _ a De M nff o vA S N0 ha hDe hD hlo hhi hN hL2
  set β : K := a ^ 12 * (De ^ M)⁻¹ with hβ
  have hβ0 : β ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe))
  have hvβ : ∀ w : Pl K, vw w β = 12 * (vw w a + M * o w) := by
    intro w
    rw [hβ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe)),
      Formalism.DivisionValues.ValuationRepresentative.vw_inv, vw_pow w a ha, vw_pow w De hDe, hD w]
    push_cast; ring
  obtain ⟨pf1, pf2⟩ := Formalism.DivisionValues.prod_formula' K β hβ0
  obtain ⟨n1, n2⟩ := sum_valuation_nat K nff
  obtain ⟨w1, w2, w3⟩ := weight_sum' K S N0
  have hfin : (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite := by
    refine (pf1.union n1).subset ?_
    intro w hw
    simp only [Function.mem_support, Set.mem_union] at hw ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2⟩ := hcon
    have hl : lw w ≠ 0 := left_ne_zero_of_mul hw
    have d1 : vw w β = 0 := by
      have := (mul_eq_zero.mp c1).resolve_left hl; exact_mod_cast this
    have d2 : vw w (nff : K) = 0 := by
      have := (mul_eq_zero.mp c2).resolve_left hl; exact_mod_cast this
    have e1 := hvβ w
    have e2 := hlo w
    have e3 := hhi w
    rw [d2] at e3
    have : vA w = 0 := by omega
    apply hw; rw [this]; simp
  refine ⟨hfin, ?_⟩
  have hpt : ∀ w : Pl K, lw w * |(vA w : ℝ)| ≤
      (1 / 12) * (lw w * (vw w β : ℝ)) + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))
        + 2 * (lw w * wt S N0 w) := by
    intro w
    have h0 := lw_nonneg w
    have h1 : ((vw w β : ℤ) : ℝ) = 12 * ((vw w a : ℝ) + M * o w) := by rw [hvβ w]; push_cast; ring
    have h2 : (vA w : ℝ) ≤ (vw w a : ℝ) + M * o w + M * vw w (nff : K) := by exact_mod_cast hhi w
    have h3 := hL2 w
    have h4 := w3 hN w
    have h5 : |(vA w : ℝ)| ≤ (vA w : ℝ) + 2 * wt S N0 w := by
      rcases abs_cases (vA w : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    have h6 : |(vA w : ℝ)| ≤ (1 / 12) * (vw w β : ℝ) + M * vw w (nff : K) + 2 * wt S N0 w := by
      rw [h1]; linarith
    calc lw w * |(vA w : ℝ)| ≤ lw w * ((1 / 12) * (vw w β : ℝ) + M * vw w (nff : K) + 2 * wt S N0 w) :=
          mul_le_mul_of_nonneg_left h6 h0
      _ = _ := by ring
  have s1 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))).Finite :=
    pf1.subset fun w hw => right_ne_zero_of_mul hw
  have s2 : (Function.support fun w : Pl K => (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite :=
    n1.subset fun w hw => right_ne_zero_of_mul hw
  have s3 : (Function.support fun w : Pl K => (2 : ℝ) * (lw w * wt S N0 w)).Finite :=
    w1.subset fun w hw => right_ne_zero_of_mul hw
  have s12 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))
      + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite :=
    (s1.union s2).subset (Function.support_add _ _)
  have s123 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))
      + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ)) + 2 * (lw w * wt S N0 w)).Finite :=
    (s12.union s3).subset (Function.support_add _ _)
  refine (finsum_le_finsum' hfin s123 hpt).trans (le_of_eq ?_)
  rw [finsum_add_distrib s12 s3, finsum_add_distrib s1 s2, ← mul_finsum, ← mul_finsum,
    ← mul_finsum, ← pf2, n2, w2]
  rfl

end Formalism.PairingDivisionLocalBalance
