import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackMetricCurvatureStatement

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open scoped Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BlockPoint

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]`. Normalize the expressions using the abelian group laws.
-/
theorem sum_range_two_mul_pairs {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

/- English proof (translation)
Use `set f : ℕ → R := fun i => (x ^ i + (-x) ^ i) * y ^ (N - i) * (N.choose i : R) with hf`. Establish `e1 : (y + x) ^ N + (y - x) ^ N = ∑ i ∈ Finset.range (N + 1), f i`. Rewrite using `[add_comm y x, sub_eq_neg_add, add_pow, add_pow, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hf]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ i ∈ Finset.range (N + 1), f i = ∑ i ∈ Finset.range (2 * (N + 1)), f i`. Rewrite using `[show 2 * (N + 1) = (N + 1) + (N + 1) by ring, Finset.sum_range_add f (N + 1) (N + 1)]`. Establish `: ∑ i ∈ Finset.range (N + 1), f (N + 1 + i) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Simplify using `[hf, Nat.choose_eq_zero_of_lt (show N < N + 1 + i by omega)]`. Rewrite using `[this, add_zero]`. Rewrite using `[e1, e2, sum_range_two_mul_pairs]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hf]`.

Rewrite using `[pow_succ (-x), pow_mul (-x), neg_sq, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_pow_add_sub_pow_even {R : Type} [CommRing R] (x y : R) (N : ℕ) :
    (y + x) ^ N + (y - x) ^ N = ∑ k ∈ Finset.range (N + 1), 2 * (N.choose (2 * k) : R) * x ^ (2 * k) * y ^ (N - 2 * k) := by
  set f : ℕ → R := fun i => (x ^ i + (-x) ^ i) * y ^ (N - i) * (N.choose i : R) with hf
  have e1 : (y + x) ^ N + (y - x) ^ N = ∑ i ∈ Finset.range (N + 1), f i := by
    rw [add_comm y x, sub_eq_neg_add, add_pow, add_pow, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]; ring
  have e2 : ∑ i ∈ Finset.range (N + 1), f i = ∑ i ∈ Finset.range (2 * (N + 1)), f i := by
    rw [show 2 * (N + 1) = (N + 1) + (N + 1) by ring, Finset.sum_range_add f (N + 1) (N + 1)]
    have : ∑ i ∈ Finset.range (N + 1), f (N + 1 + i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hf, Nat.choose_eq_zero_of_lt (show N < N + 1 + i by omega)]
    rw [this, add_zero]
  rw [e1, e2, sum_range_two_mul_pairs]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hf]
  rw [pow_succ (-x), pow_mul (-x), neg_sq, ← pow_mul]
  ring

/- English proof (translation)
Introduce `hC k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ a b`. Use `set v : Fin 2 → MvPolynomial (Fin 3) ℝ := ![X 0 + X 1, X 2] with hv`. Establish `key : ∀ j : ℕ, 2 * j ≤ d + 2 → ∀ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous (d + 2 - 2 * j) → Φ ((X 1 - X 0) ^ (2 * j) * aeval v P) = oddHarm j * Ψ ((X 1 - X 0) ^ (2 * j - 1) * aeval v P)`. Introduce `j hj P hP`. Break down `Nat.eq_zero_or_pos j with rfl | hj0` into its components or cases.

Simplify using `using GlobalTheory.T.arFun_aeval_gr_sum_eq_zero_of_flagBundle_rank_two hC k B Y q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ P hP`. Conclude with `GlobalTheory.T.flag_bundle_pullback_metric_curvature hC k B Y q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ j P hj0 hj hP`. Use `set c : ℝ := ((a : ℝ) + b) / 2 with hc`. Use `set t : ℝ := ((b : ℝ) - a) / 2 with ht`. Use `set m : MvPolynomial (Fin 3) ℝ := C c * (X 0 + X 1) + X 2 with hm`.

Use `set u : MvPolynomial (Fin 3) ℝ := X 1 - X 0 with hu`. Establish `hCa : (C (a : ℝ) : MvPolynomial (Fin 3) ℝ) = C c - C t` using `by rw [← map_sub]; congr 1; rw [hc, ht]; ring`. Establish `hCb : (C (b : ℝ) : MvPolynomial (Fin 3) ℝ) = C c + C t` using `by rw [← map_add]; congr 1; rw [hc, ht]; ring`. Establish `l1 : lin ![(a : ℝ), b, 1] = m + C t * u`. Simplify using `only [lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, hCa, hCb, hm, hu]`.

Expand and normalize the polynomial expressions, which then agree. Establish `l2 : lin ![(b : ℝ), a, 1] = m - C t * u`. Simplify using `only [lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, hCa, hCb, hm, hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmv : ∀ e : ℕ, m ^ e = aeval v ((C c * X 0 + X 1) ^ e)`.

Introduce `e`. Simplify using `[hv, hm, map_pow, aeval_X, MvPolynomial.algebraMap_eq]`. Establish `hhom : ∀ e : ℕ, ((C c * X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ^ e).IsHomogeneous e`. Introduce `e`. Establish `h1 : (C c * X 0 + X 1 : MvPolynomial (Fin 2) ℝ).IsHomogeneous 1` using `((isHomogeneous_X _ _).C_mul _).add (isHomogeneous_X _ _)`.

Simplify using `using h1.pow e`. Rewrite using `[← map_add, l1, l2, add_pow_add_sub_pow_even, map_sum, swapG, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : 2 * j ≤ d + 2`. Establish `e` using `key j hj _ (hhom (d + 2 - 2 * j))`.

Rewrite `e` using `[← hmv]`. Rewrite using `[show (2 * ((d + 2).choose (2 * j) : MvPolynomial (Fin 3) ℝ) * (C t * u) ^ (2 * j) * m ^ (d + 2 - 2 * j)) = C (2 * ((d + 2).choose (2 * j) : ℝ) * t ^ (2 * j)) * (u ^ (2 * j) * m ^ (d + 2 - 2 * j)) by`. Simplify using `only [map_mul, map_pow, map_natCast, map_ofNat]`. Use the proof step `ring_nf]`. Rewrite using `[C_mul', map_smul, smul_eq_mul, C_mul', map_smul, smul_eq_mul, e]`.

Simplify using `only [ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (d + 2).choose (2 * j) = 0` using `Nat.choose_eq_zero_of_lt (by omega)`. Simplify using `[h0]`.
-/
theorem swapReg_swapG : ArCalc → SwapReg swapG := by
  intro hC k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ a b
  set v : Fin 2 → MvPolynomial (Fin 3) ℝ := ![X 0 + X 1, X 2] with hv
  have key : ∀ j : ℕ, 2 * j ≤ d + 2 → ∀ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous (d + 2 - 2 * j) →
      Φ ((X 1 - X 0) ^ (2 * j) * aeval v P) = oddHarm j * Ψ ((X 1 - X 0) ^ (2 * j - 1) * aeval v P) := by
    intro j hj P hP
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using GlobalTheory.T.arFun_aeval_gr_sum_eq_zero_of_flagBundle_rank_two hC k B Y q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ P hP
    · exact GlobalTheory.T.flag_bundle_pullback_metric_curvature hC k B Y q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ j P hj0 hj hP
  set c : ℝ := ((a : ℝ) + b) / 2 with hc
  set t : ℝ := ((b : ℝ) - a) / 2 with ht
  set m : MvPolynomial (Fin 3) ℝ := C c * (X 0 + X 1) + X 2 with hm
  set u : MvPolynomial (Fin 3) ℝ := X 1 - X 0 with hu
  have hCa : (C (a : ℝ) : MvPolynomial (Fin 3) ℝ) = C c - C t := by rw [← map_sub]; congr 1; rw [hc, ht]; ring
  have hCb : (C (b : ℝ) : MvPolynomial (Fin 3) ℝ) = C c + C t := by rw [← map_add]; congr 1; rw [hc, ht]; ring
  have l1 : lin ![(a : ℝ), b, 1] = m + C t * u := by
    simp only [lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, hCa, hCb, hm, hu]
    ring
  have l2 : lin ![(b : ℝ), a, 1] = m - C t * u := by
    simp only [lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, hCa, hCb, hm, hu]
    ring
  have hmv : ∀ e : ℕ, m ^ e = aeval v ((C c * X 0 + X 1) ^ e) := by
    intro e
    simp [hv, hm, map_pow, aeval_X, MvPolynomial.algebraMap_eq]
  have hhom : ∀ e : ℕ, ((C c * X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ^ e).IsHomogeneous e := by
    intro e
    have h1 : (C c * X 0 + X 1 : MvPolynomial (Fin 2) ℝ).IsHomogeneous 1 :=
      ((isHomogeneous_X _ _).C_mul _).add (isHomogeneous_X _ _)
    simpa using h1.pow e
  rw [← map_add, l1, l2, add_pow_add_sub_pow_even, map_sum, swapG, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : 2 * j ≤ d + 2
  · have e := key j hj _ (hhom (d + 2 - 2 * j))
    rw [← hmv] at e
    rw [show (2 * ((d + 2).choose (2 * j) : MvPolynomial (Fin 3) ℝ) * (C t * u) ^ (2 * j) * m ^ (d + 2 - 2 * j)) =
        C (2 * ((d + 2).choose (2 * j) : ℝ) * t ^ (2 * j)) * (u ^ (2 * j) * m ^ (d + 2 - 2 * j)) by
          simp only [map_mul, map_pow, map_natCast, map_ofNat]; ring_nf]
    rw [C_mul', map_smul, smul_eq_mul, C_mul', map_smul, smul_eq_mul, e]
    simp only [ht]
    ring
  · have h0 : (d + 2).choose (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

end GlobalTheory.BlockPoint
end
