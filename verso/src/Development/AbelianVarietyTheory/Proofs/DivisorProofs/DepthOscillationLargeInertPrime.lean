import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.InertOsc

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

/- English proof (translation)
Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Conclude with `GlobalTheory.LamF.card_psiSet H`.
-/
theorem card_filter_inPsi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    [DecidablePred (fun τ : E →+* ℂ => InPsi H τ)] :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact GlobalTheory.LamF.card_psiSet H

/- English proof (translation)
Introduce `T io e ho y` and use `⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩`.
-/
theorem nuBetween_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c}
    {cx : Lt1 Dw → ℕ} {A B B' : ℝ} (h : NuBetween Xo la cx A B) (hB : B ≤ B') : NuBetween Xo la cx A B' :=
  fun T io e ho y => ⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩

/- English proof (translation)
Establish `h1 : 2 * m ≤ m * p` using `by nlinarith`. Establish `h2 : q * p ≤ m * p` using `Nat.mul_le_mul_right _ hq`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem big_arith {i q k m p : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    2 * i + 2 * q * p ≤ 5 * m * p := by
  have h1 : 2 * m ≤ m * p := by nlinarith
  have h2 : q * p ≤ m * p := Nat.mul_le_mul_right _ hq
  nlinarith

/- English proof (translation)
Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (by omega : 0 < p)`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1`. Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ)` using `by exact_mod_cast big_arith hi hk hq hp`.

Move the coercions through the operations in `at hn`. Unfold `boundInert`. Rewrite using `[div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]`. Establish `hc : (0 : ℝ) ≤ c` using `Nat.cast_nonneg _`. Establish `: (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1) = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2` using `by ring`.

Rewrite using `[this]`. Establish `: 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2` using `by ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)`.
-/
theorem big_bound {i q k m p c : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    boundInert p q i c ≤ 5 * (m : ℝ) * c / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ) := by exact_mod_cast big_arith hi hk hq hp
  push_cast at hn
  unfold boundInert
  rw [div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have : (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1)
      = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  have : 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)

/- English proof (translation)
Establish `h` using `rk_le f`. Unfold `Datum.mult at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
theorem rk_add_one_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (f : Lt1 Dw) : rk f + 1 ≤ Dw.p + Dw.q + 1 := by
  have h := rk_le f
  unfold Datum.mult at h
  split_ifs at h <;> omega

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp`. Take `⟨hS1, hSq, hmk, hm1, hk2, hF⟩` from `hS`. Take `⟨hMb, hbig, hsm, -⟩` from `hE`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1`.

Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp2`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `la`. Use `set w : Lt1 Dw → ℝ := fun f => if IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1) else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw`. Establish `key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f`.

Introduce `f`. Distinguish the cases in `hb : IsBig k f`. Take `⟨A, B, hAB, hBA⟩` from `GlobalTheory.T.factorDepth_bounds_inert_prime E H Dw l Xo c p la hdisc hin f (cx f) hb.1`. Use `⟨(A, B), hAB, ?_⟩` and prove the remaining obligations. Simplify using `only [hw, if_pos hb]`.

Conclude with `hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)`. Use `⟨(0, boundAll p (rk f) (cx f)), (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, ?_⟩` and prove the remaining obligations. Simplify using `only [hw, if_neg hb, boundAll, sub_zero, le_refl]`. Use `choose g hg using key`. Take `⟨n, hn⟩` from `((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2`.

Use `⟨n, nuBetween_mono hn ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f` using `Finset.sum_le_sum fun f _ => (hg f).2`. It suffices to establish `hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith`. Establish `hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F`. Rewrite using `[card_filter_inPsi H, hF]`.

Use linear arithmetic over natural numbers and integers. Establish `hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ F * Mb`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => IsBig k f)) (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1) (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations.

Establish `h` using `hbig τ`. Move the coercions through the operations in `at h`. Rewrite using `[Finset.filter_filter]`. Use `h using 2` and compare the differences between its conclusion and the goal. Use `_ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]`.

Establish `hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ)`. Unfold `sumSmallSpread`. Use `push_cast`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `f`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]`. Simplify using `only [hw]`. Rewrite using `[Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]`. Use `div_le_div_of_nonneg_right ?_ hp1.le` and prove the remaining obligations. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`.

Establish `h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb)` using `mul_le_mul_of_nonneg_left hB (by positivity)`. Establish `h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb`. Establish `: (0 : ℝ) ≤ F * m * Mb` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem oscLe_inert_large : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  classical
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp
  obtain ⟨hS1, hSq, hmk, hm1, hk2, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  intro la
  set w : Lt1 Dw → ℝ := fun f => if IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1)
    else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw
  have key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f := by
    intro f
    by_cases hb : IsBig k f
    · obtain ⟨A, B, hAB, hBA⟩ := GlobalTheory.T.factorDepth_bounds_inert_prime E H Dw l Xo c p la hdisc hin f (cx f) hb.1
      refine ⟨(A, B), hAB, ?_⟩
      simp only [hw, if_pos hb]
      exact hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)
    · refine ⟨(0, boundAll p (rk f) (cx f)), (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, ?_⟩
      simp only [hw, if_neg hb, boundAll, sub_zero, le_refl]
  choose g hg using key
  obtain ⟨n, hn⟩ := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2
  refine ⟨n, nuBetween_mono hn ?_⟩
  have hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => (hg f).2
  suffices hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith

  have hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi H, hF]; omega
  have hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ F * Mb := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => IsBig k f))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]
    calc _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), Mb := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have h := hbig τ
          push_cast at h
          rw [Finset.filter_filter]
          convert h using 2
      _ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ) := by
    unfold sumSmallSpread
    push_cast
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]
  simp only [hw]
  rw [Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]
  refine div_le_div_of_nonneg_right ?_ hp1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb := by
    have : (0 : ℝ) ≤ F * m * Mb := by positivity
    nlinarith
  linarith

end GlobalTheory.RefSum.InertOsc
