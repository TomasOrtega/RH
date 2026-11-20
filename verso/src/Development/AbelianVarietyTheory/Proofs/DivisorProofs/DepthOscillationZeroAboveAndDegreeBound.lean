import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

open Classical in

/- English proof (translation)
Establish `h` using `GlobalTheory.LamF.card_psiSet H`. Rewrite `h` using `[hF]`. Establish `h2 : Nat.card (GlobalTheory.LamF.psiSet H) = (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card`. Rewrite using `[Nat.card_eq_fintype_card, ← Fintype.card_subtype]`. Both sides reduce to the same expression.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_filter_inPsi_of_finrank {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {F : ℕ} (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
  have h := GlobalTheory.LamF.card_psiSet H
  rw [hF] at h
  have h2 : Nat.card (GlobalTheory.LamF.psiSet H) = (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  omega

open Classical in

/- English proof (translation)
Take `⟨hMb, hbig, hsm, -⟩` from `hE`. Establish `hF : Module.finrank ℚ E = 2 * F` using `hS.2.2.2.2.2`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (IsBig k)]`. Use `add_le_add ?_ ?_` and prove the remaining obligations. Establish `hB : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) ≤ F * Mb`.

Rewrite using `[← Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Use `split_ifs with hτ`. Use `hbig τ` as an intermediate fact.

Rewrite using `[Finset.filter_filter]`. Move the coercions through the operations in `at this`. Use `this using 3` and compare the differences between its conclusion and the goal. Apply `le_of_eq` to reduce the goal to its premises. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `f hf`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hf`. Conclude with `absurd (hf.2 ▸ hf.1.1) hτ`. Use `_ = F * Mb := by`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, card_filter_inPsi_of_finrank H hF, nsmul_eq_mul]`.

Establish `hN : ∀ f : Lt1 Dw, (rk f : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ)`. Introduce `f`. Establish `h1` using `rk_le f`. Establish `h2 : Dw.mult f.1 ≤ Dw.p + Dw.q`. Apply the tactic sequence `unfold Datum.mult; split_ifs <;> omega`.

Conclude with `h1.trans h2` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `he : ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * (cx f : ℝ) = (sumSmallSpread k cx : ℝ)`. Unfold `sumSmallSpread`. Use `push_cast`.

Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `f`. Simplify using `[not_isBig_iff]`. Rewrite using `[he]`. Conclude with `hsm`.
-/
theorem degree_le_of_exponentBound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} (hS : Shape Dw F k m) (hE : ExpBd Dw k cx Mb Sm M) :
    (∑ f : Lt1 Dw, (rk f : ℝ) * (cx f : ℝ)) ≤ F * (Dw.p + Dw.q : ℕ) * Mb + Sm := by
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hF : Module.finrank ℚ E = 2 * F := hS.2.2.2.2.2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (IsBig k)]
  refine add_le_add ?_ ?_
  · have hB : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) ≤ F * Mb := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)]
      calc ∑ τ : E →+* ℂ, ∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ)
          ≤ ∑ τ : E →+* ℂ, if InPsi H τ then Mb else 0 := by
            refine Finset.sum_le_sum fun τ _ => ?_
            split_ifs with hτ
            · have := hbig τ
              rw [Finset.filter_filter]
              push_cast at this
              convert this using 3
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
              exact absurd (hf.2 ▸ hf.1.1) hτ
        _ = F * Mb := by
            rw [← Finset.sum_filter, Finset.sum_const, card_filter_inPsi_of_finrank H hF, nsmul_eq_mul]
    have hN : ∀ f : Lt1 Dw, (rk f : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
      intro f
      have h1 := rk_le f
      have h2 : Dw.mult f.1 ≤ Dw.p + Dw.q := by
        unfold Datum.mult; split_ifs <;> omega
      exact_mod_cast h1.trans h2
    calc ∑ f ∈ Finset.univ.filter (IsBig k), (rk f : ℝ) * (cx f : ℝ)
        ≤ ∑ f ∈ Finset.univ.filter (IsBig k), ((Dw.p + Dw.q : ℕ) : ℝ) * (cx f : ℝ) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hN f) (Nat.cast_nonneg _)
      _ = ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) * (F * Mb) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = F * (Dw.p + Dw.q : ℕ) * Mb := by ring
  · have he : ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * (cx f : ℝ) = (sumSmallSpread k cx : ℝ) := by
      unfold sumSmallSpread
      push_cast
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext f
      simp [not_isBig_iff]
    rw [he]; exact hsm

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _`. Establish `hp : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Prove the components needed by the constructor for the conclusion. Introduce `hMp la`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `h` using `((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun _ => 0) (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).2 (lt_of_le_of_lt (hE.2.2.2 f) hMp))).1`. Simplify using `using h`. Introduce `la`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `h` using `((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun f => boundAll p (rk f) (cx f)) (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1)).1`.

Establish `hsum : ∑ f, boundAll p (rk f) (cx f) ≤ (F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)`. Unfold `boundAll`. Rewrite using `[← Finset.sum_div]`. Conclude with `div_le_div_of_nonneg_right (degree_le_of_exponentBound hS hE) (by linarith)`. Introduce `T io e ho y`.

Take `⟨h1, h2⟩` from `h T io e ho y`. Use `⟨by simpa using h1, fun ha => (h2 ha).trans ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_const_zero, Nat.cast_zero, zero_add]`. Conclude with `EReal.coe_le_coe_iff.2 hsum`.
-/
theorem oscLe_zero_above_and_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  constructor
  · intro hMp la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun _ => 0)
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).2 (lt_of_le_of_lt (hE.2.2.2 f) hMp))).1
    simpa using h
  · intro la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun f => boundAll p (rk f) (cx f))
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1)).1
    have hsum : ∑ f, boundAll p (rk f) (cx f) ≤ (F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1) := by
      unfold boundAll
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (degree_le_of_exponentBound hS hE) (by linarith)
    intro T io e ho y
    obtain ⟨h1, h2⟩ := h T io e ho y
    refine ⟨by simpa using h1, fun ha => (h2 ha).trans ?_⟩
    simp only [Finset.sum_const_zero, Nat.cast_zero, zero_add]
    exact EReal.coe_le_coe_iff.2 hsum

end GlobalTheory.RefSum
