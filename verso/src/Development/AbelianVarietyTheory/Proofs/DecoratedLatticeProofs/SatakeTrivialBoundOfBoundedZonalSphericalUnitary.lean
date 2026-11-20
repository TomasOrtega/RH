import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GradedSeriesMulNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOutStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEqStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.ZonalBound

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `e : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ (n - 1)`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]`. Establish `e' : ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) = ((q : ℝ) ^ (n - 1))⁻¹`. Rewrite using `[Real.rpow_neg (by positivity), e]`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound`. Rewrite using `[e, e']`. Use `forall_congr' fun i => and_congr ?_ Iff.rfl |>.trans and_comm` and prove the remaining obligations. Establish `hp : 0 < ‖(β i : ℂ)‖` using `norm_pos_iff.2 (β i).ne_zero`. Conclude with `⟨fun h => inv_le_of_inv_le₀ (by positivity) h, fun h => inv_le_of_inv_le₀ hp h⟩`.
-/
theorem trivialBound_iff {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (β : Fin (n / 2) → ℂˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β ↔
      ∀ i, ‖(β i : ℂ)‖ ≤ (q : ℝ) ^ (n - 1) ∧ ‖(β i : ℂ)‖⁻¹ ≤ (q : ℝ) ^ (n - 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have e : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ (n - 1) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]
  have e' : ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) = ((q : ℝ) ^ (n - 1))⁻¹ := by
    rw [Real.rpow_neg (by positivity), e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound
  rw [e, e']
  refine forall_congr' fun i => and_congr ?_ Iff.rfl |>.trans and_comm
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  exact ⟨fun h => inv_le_of_inv_le₀ (by positivity) h, fun h => inv_le_of_inv_le₀ hp h⟩

/- English proof (translation)
Break down `Nat.lt_or_ge n 2 with hn | hn` into its components or cases. Introduce `i; exact absurd i.2 (by omega)`. Rewrite using `[trivialBound_iff hq (by omega)]`. Introduce `i`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`.

Use `set c : ℝ := (q : ℝ) ^ (n - 1) with hc`. Establish `hc0 : 0 < c` using `by positivity`. Establish `hcc : (q : ℝ) ^ (2 * (n - 1)) = c * c` using `by rw [hc, ← pow_add]; ring_nf`. Establish `hcC : ‖((q : ℂ) ^ (n - 1))‖ = c` using `by rw [norm_pow, Complex.norm_natCast]`. Establish `hcC0 : ((q : ℂ) ^ (n - 1)) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))`.

Establish `hp : 0 < ‖(β i : ℂ)‖` using `norm_pos_iff.2 (β i).ne_zero`. Establish `hb0 : (β i : ℂ) ≠ 0` using `(β i).ne_zero`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hlt push_neg at hlt`. Establish `hX : ‖((q : ℂ) ^ (n - 1) * (β i : ℂ))⁻¹‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹`.

Rewrite using `[norm_inv, norm_mul, hcC, hcc]`. Conclude with `inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hlt hc0)`. Apply `(h i _ hX).1` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Assume the negation of the conclusion as `hlt push_neg at hlt`. Establish `hX : ‖(β i : ℂ) / (q : ℂ) ^ (n - 1)‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹`. Rewrite using `[norm_div, hcC, hcc, div_lt_iff₀ hc0, mul_inv, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]`. Conclude with `(lt_inv_comm₀ hp hc0).2 hlt`. Apply `(h i _ hX).2` to reduce the goal to its premises.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trivialBound_of_ne_zero {q n : ℕ} (hq : 1 ≤ q) (β : Fin (n / 2) → ℂˣ)
    (h : ∀ i, ∀ X : ℂ, ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ →
      1 - (q : ℂ) ^ (n - 1) * X * (β i : ℂ) ≠ 0 ∧ 1 - (q : ℂ) ^ (n - 1) * X / (β i : ℂ) ≠ 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  rw [trivialBound_iff hq (by omega)]
  intro i
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set c : ℝ := (q : ℝ) ^ (n - 1) with hc
  have hc0 : 0 < c := by positivity
  have hcc : (q : ℝ) ^ (2 * (n - 1)) = c * c := by rw [hc, ← pow_add]; ring_nf
  have hcC : ‖((q : ℂ) ^ (n - 1))‖ = c := by rw [norm_pow, Complex.norm_natCast]
  have hcC0 : ((q : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  have hb0 : (β i : ℂ) ≠ 0 := (β i).ne_zero
  constructor
  · by_contra hlt
    push_neg at hlt
    have hX : ‖((q : ℂ) ^ (n - 1) * (β i : ℂ))⁻¹‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_inv, norm_mul, hcC, hcc]
      exact inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hlt hc0)
    apply (h i _ hX).1
    field_simp
    ring
  · by_contra hlt
    push_neg at hlt
    have hX : ‖(β i : ℂ) / (q : ℂ) ^ (n - 1)‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_div, hcC, hcc, div_lt_iff₀ hc0, mul_inv, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]
      exact (lt_inv_comm₀ hp hc0).2 hlt
    apply (h i _ hX).2
    field_simp
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

def denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ))) * (if Odd n then 1 - c * X else 1)

/- English proof (translation)
Unfold `denom`. Distinguish the cases in `h : Odd n`. Simplify using `only [if_pos h]`. Use `fun_prop`. Simplify using `only [if_neg h]`.

Use `fun_prop`.
-/
theorem differentiable_denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) : Differentiable ℂ (denom n c α) := by
  unfold denom
  by_cases h : Odd n
  · simp only [if_pos h]; fun_prop
  · simp only [if_neg h]; fun_prop

/- English proof (translation)
Introduce `e` and use `by rw [← sub_eq_zero.1 e, norm_one] at h exact lt_irrefl _ h`.
-/
theorem one_sub_ne_zero {z : ℂ} (h : ‖z‖ < 1) : 1 - z ≠ 0 := fun e => by
  rw [← sub_eq_zero.1 e, norm_one] at h
  exact lt_irrefl _ h

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
/- English proof (translation)
Establish `h1 : (∏ i, (1 - c * X * (α i : ℂ))⁻¹ * (1 - c * X / (α i : ℂ))⁻¹) * ∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ)) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `a : 1 - c * X * (α i : ℂ) ≠ 0` using `one_sub_ne_zero (by rw [norm_mul]; exact (h.2 i).1)`. Establish `b : 1 - c * X / (α i : ℂ) ≠ 0` using `one_sub_ne_zero (by rw [norm_div, div_eq_mul_inv]; exact (h.2 i).2)`.

Rewrite using `[mul_mul_mul_comm, inv_mul_cancel₀ a, inv_mul_cancel₀ b, one_mul]`. Establish `h2 : (if Odd n then (1 - c * X)⁻¹ else 1) * (if Odd n then 1 - c * X else 1) = 1` using `by split_ifs`. Conclude with `inv_mul_cancel₀ (one_sub_ne_zero h.1)`. Conclude with `one_mul _`. Rewrite using `[closedForm, denom, mul_assoc (∏ j ∈ Finset.range n, _), mul_assoc (∏ j ∈ Finset.range n, _), mul_mul_mul_comm, h1, h2, one_mul, mul_one]`.
-/
theorem closedForm_mul_denom (q n : ℕ) (c X : ℂ) (α : Fin (n / 2) → ℂˣ) (h : Domain (c * X) α) :
    closedForm q n X (c * X) α * denom n c α X = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) := by
  have h1 : (∏ i, (1 - c * X * (α i : ℂ))⁻¹ * (1 - c * X / (α i : ℂ))⁻¹) *
      ∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    have a : 1 - c * X * (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_mul]; exact (h.2 i).1)
    have b : 1 - c * X / (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_div, div_eq_mul_inv]; exact (h.2 i).2)
    rw [mul_mul_mul_comm, inv_mul_cancel₀ a, inv_mul_cancel₀ b, one_mul]
  have h2 : (if Odd n then (1 - c * X)⁻¹ else 1) * (if Odd n then 1 - c * X else 1) = 1 := by
    split_ifs
    · exact inv_mul_cancel₀ (one_sub_ne_zero h.1)
    · exact one_mul _
  rw [closedForm, denom, mul_assoc (∏ j ∈ Finset.range n, _), mul_assoc (∏ j ∈ Finset.range n, _),
    mul_mul_mul_comm, h1, h2, one_mul, mul_one]

/- English proof (translation)
Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Use `Finset.prod_ne_zero_iff.2 fun j hj => one_sub_ne_zero ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.1 hj`. Rewrite using `[norm_mul, norm_pow, norm_neg, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem numer_ne_zero {q n : ℕ} (hq : 1 ≤ q) {X : ℂ} (hX : ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹) :
    ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) ≠ 0 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine Finset.prod_ne_zero_iff.2 fun j hj => one_sub_ne_zero ?_
  have hj' := Finset.mem_range.1 hj
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
  calc (q : ℝ) ^ j * ‖X‖ ≤ (q : ℝ) ^ (2 * (n - 1)) * ‖X‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega)) (norm_nonneg _)
    _ < (q : ℝ) ^ (2 * (n - 1)) * ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := mul_lt_mul_of_pos_left hX (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

/- English proof (translation)
Establish `key : ∀ a : ℝ, a ≤ M → ‖y‖ * a < 1` using `fun a ha => (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_lt hy`. Conclude with `⟨by simpa using key 1 hM, fun i => ⟨key _ (hα i).1, key _ (hα i).2⟩⟩`.
-/
theorem domain_of_bound {r : ℕ} {y : ℂ} {α : Fin r → ℂˣ} {M : ℝ} (hM : 1 ≤ M)
    (hα : ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M) (hy : ‖y‖ * M < 1) : Domain y α := by
  have key : ∀ a : ℝ, a ≤ M → ‖y‖ * a < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_lt hy
  exact ⟨by simpa using key 1 hM, fun i => ⟨key _ (hα i).1, key _ (hα i).2⟩⟩

/- English proof (translation)
Establish `h0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ ‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹` using `fun i _ => by positivity`. Use `⟨1 + ∑ i, (‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹), le_add_of_nonneg_right (Finset.sum_nonneg h0), fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `Finset.single_le_sum h0 (Finset.mem_univ i)`. Establish `h2 : 0 ≤ ‖(α i : ℂ)‖` using `norm_nonneg _`. Establish `h3 : 0 ≤ ‖(α i : ℂ)‖⁻¹` using `by positivity`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem exists_bound {r : ℕ} (α : Fin r → ℂˣ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M := by
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ ‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹ := fun i _ => by positivity
  refine ⟨1 + ∑ i, (‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹), le_add_of_nonneg_right (Finset.sum_nonneg h0), fun i => ?_⟩
  have h1 := Finset.single_le_sum h0 (Finset.mem_univ i)
  have h2 : 0 ≤ ‖(α i : ℂ)‖ := norm_nonneg _
  have h3 : 0 ≤ ‖(α i : ℂ)‖⁻¹ := by positivity
  constructor <;> linarith

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

/- English proof (translation)
Establish `hq2 : 2 ≤ q` using `hU.2.2.2.2.2.1`. Establish `hq : q ≠ 0` using `by omega`. Establish `hqC : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Establish `hc` using `GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU`. Use `choose D t ht k₁ hk₁ k₂ hk₂ e using hc`.

Use `⟨fun a => (∑ i, max (D a.out i) 0).toNat, fun X hX => ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ, hχϖ⟩` from `GlobalTheory.ZetaSumU.exists_unr_char ϖ hU (Units.mk0 (X * (q : ℂ) ^ n) (mul_ne_zero hX (pow_ne_zero _ hqC)))`. Take `⟨Φ, hΦ⟩` from `exists_isSphSec σ hq n hχ (((0 : ℕ) : ℂ) / 2)`. Take `⟨hXe, hYe⟩` from `GlobalTheory.ZetaSumU.varXY_eq q n 0 hq2 (X * (q : ℂ) ^ n)`. Establish `hz : ((χ ϖ : ℂˣ) : ℂ) = X * (q : ℂ) ^ n` using `by rw [hχϖ]; rfl`.

Establish `hvX : varX q n (χ ϖ) (((0 : ℕ) : ℂ) / 2) = X`. Rewrite using `[hz, hXe, add_zero, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqC), mul_one]`. Establish `hval : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = X ^ (∑ i, max (D g i) 0)` using `fun g k hk => by`. Establish `h` using `GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ _ Φ hΦ (D g) (t g) (ht g) (k₁ g) (hk₁ g) (k₂ g * k) (mul_mem (hk₂ g) hk)`. Rewrite `h` using `[hvX, ← mul_assoc, ← e g]`.

Conclude with `h`. Establish `hval1 : ∀ g, Φ (io1 σ n g) = X ^ (∑ i, max (D g i) 0)` using `fun g => by`. Simplify `hval g 1 (one_mem _)` using `only [mul_one]`. Use `⟨χ, _, Φ, hχ, hΦ, hvX, ?_, fun g k hk => (hval g k hk).trans (hval1 g).symm, fun a => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' hn`.

Rewrite using `[hz, hYe, Nat.add_sub_cancel, zero_add, pow_one, pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hval1, ← zpow_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)]`.
-/
theorem exists_deg {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ)
    {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (hn : 1 ≤ n) :
    ∃ deg : GU σ n ⧸ KU σ n → ℕ, ∀ X : ℂ, X ≠ 0 → ∃ (χ : Lˣ →* ℂˣ) (s : ℂ) (Φ : GD σ n → ℂ), IsUnr χ ∧
      IsSphSec σ q n χ s Φ ∧ varX q n (χ ϖ) s = X ∧ varY q (χ ϖ) s = (q : ℂ) ^ (n - 1) * X ∧
      (∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = Φ (io1 σ n g)) ∧
      ∀ a : GU σ n ⧸ KU σ n, Φ (io1 σ n a.out) = X ^ deg a := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hc := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU
  choose D t ht k₁ hk₁ k₂ hk₂ e using hc
  refine ⟨fun a => (∑ i, max (D a.out i) 0).toNat, fun X hX => ?_⟩
  obtain ⟨χ, hχ, hχϖ⟩ := GlobalTheory.ZetaSumU.exists_unr_char ϖ hU
    (Units.mk0 (X * (q : ℂ) ^ n) (mul_ne_zero hX (pow_ne_zero _ hqC)))
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq n hχ (((0 : ℕ) : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := GlobalTheory.ZetaSumU.varXY_eq q n 0 hq2 (X * (q : ℂ) ^ n)
  have hz : ((χ ϖ : ℂˣ) : ℂ) = X * (q : ℂ) ^ n := by rw [hχϖ]; rfl
  have hvX : varX q n (χ ϖ) (((0 : ℕ) : ℂ) / 2) = X := by
    rw [hz, hXe, add_zero, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqC), mul_one]
  have hval : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = X ^ (∑ i, max (D g i) 0) := fun g k hk => by
    have h := GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ _ Φ hΦ (D g) (t g) (ht g) (k₁ g) (hk₁ g) (k₂ g * k)
      (mul_mem (hk₂ g) hk)
    rw [hvX, ← mul_assoc, ← e g] at h
    exact h
  have hval1 : ∀ g, Φ (io1 σ n g) = X ^ (∑ i, max (D g i) 0) := fun g => by
    simpa only [mul_one] using hval g 1 (one_mem _)
  refine ⟨χ, _, Φ, hχ, hΦ, hvX, ?_, fun g k hk => (hval g k hk).trans (hval1 g).symm, fun a => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [hz, hYe, Nat.add_sub_cancel, zero_add, pow_one, pow_succ]
    field_simp
  · rw [hval1, ← zpow_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

/- English proof (translation)
Introduce `H L _ _ _ ϖ σ q n hU α w hw hb`. Take `⟨C, hC⟩` from `hb`. Break down `Nat.lt_or_ge n 2 with hn | hn` into its components or cases. Introduce `i; exact absurd i.2 (by omega)`. Establish `hq2 : 2 ≤ q` using `hU.2.2.2.2.2.1`.

Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast (by omega : 1 ≤ q)`. Take `⟨deg, hdeg⟩` from `exists_deg ϖ hU (by omega : 1 ≤ n)`. Use `letI : MeasurableSpace (GU σ n) := borel _`. Use `haveI : BorelSpace (GU σ n) := ⟨rfl⟩`. Take `⟨μ, hμH, hμK⟩` from `GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n`.

Establish `hKo` using `(GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L (ϖ : L) σ q n hU).1`. Establish `hc1 : (1 : ℝ) ≤ (q : ℝ) ^ (n - 1)` using `one_le_pow₀ hq1`. Establish `hc0 : (0 : ℝ) < (q : ℝ) ^ (n - 1)` using `by positivity`. Establish `hny : ∀ x : ℝ, 0 < x → ‖(q : ℂ) ^ (n - 1) * (x : ℂ)‖ = (q : ℝ) ^ (n - 1) * x` using `fun x hx => by`. Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hx.le]`.

Take `⟨α0, hα0, hw0⟩` from `isZonal_one hU n`. Establish `hb0` using `(trivialBound_iff (by omega) (by omega) α0).1 (GlobalTheory.ZetaSumU.tb_triv q n hq2 α0 hα0)`. Establish `hsum : ∀ r : ℝ, 0 < r → r < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ → Summable fun a => r ^ deg a` using `fun r hr hρ => by`. Take `⟨χ, s, Φ, hχ, hΦ, -, hY, hinv, hval⟩` from `hdeg (r : ℂ) (by exact_mod_cast hr.ne')`. Establish `hdom : Domain (varY q (χ ϖ) s) α0`.

Rewrite using `[hY]`. Use `domain_of_bound hc1 hb0 ?_` and prove the remaining obligations. Rewrite using `[hny r hr, mul_right_comm, ← pow_add, ← two_mul]`. Conclude with `(mul_lt_mul_of_pos_left hρ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))`. Establish `hint` using `((H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α0 _ hw0).1 hdom).1`.

Establish `hs` using `GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ (fun g k hk => by simp only [hinv g k hk]) hint`. Use `hs.congr fun a => ?_` and prove the remaining obligations. Simplify using `only [hval, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]`. Take `⟨M, hM, hαM⟩` from `exists_bound α`. Establish `heq : ∀ x : ℝ, 0 < x → x < ((q : ℝ) ^ (n - 1) * M)⁻¹ → (∑' a : GU σ n ⧸ KU σ n, w a.out * (x : ℂ) ^ deg a) * denom n ((q : ℂ) ^ (n - 1)) α x = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * (x : ℂ))` using `fun x hx hδ => by`.

Take `⟨χ, s, Φ, hχ, hΦ, hX, hY, hinv, hval⟩` from `hdeg (x : ℂ) (by exact_mod_cast hx.ne')`. Establish `hdom : Domain ((q : ℂ) ^ (n - 1) * (x : ℂ)) α`. Use `domain_of_bound hM hαM ?_` and prove the remaining obligations. Rewrite using `[hny x hx, mul_right_comm]`. Conclude with `(mul_lt_mul_of_pos_left hδ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))`.

Take `⟨hint, hI, -⟩` from `(H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α w hw).1 (by rw [hY]; exact hdom)`. Establish `hF : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) * w (g * k) = Φ (io1 σ n g) * w g` using `fun g k hk => by`. Establish `h1` using `hw.1 1 ⟨k, hk⟩ g`. Simplify using `only [OneMemClass.coe_one, one_mul] at h1`. Rewrite using `[hinv g k hk, h1]`.

Establish `hs` using `(GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm`. Establish `hci` using `(GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK (fun g => Φ (io1 σ n g) * w g) _ hF hs.hasSum).2`. Rewrite `hci` using `[hI, hX, hY]`. Rewrite using `[← closedForm_mul_denom q n _ _ α hdom, hci]`. Use `congr 1`.

Conclude with `tsum_congr fun a => by rw [hval, mul_comm]`. Use `trivialBound_of_ne_zero (by omega) α fun i X hX => ?_` and prove the remaining obligations. Establish `hP` using `GlobalTheory.gradedSeries_mul_ne_zero (GU σ n ⧸ KU σ n) deg (fun a => w a.out) ((q : ℝ) ^ (2 * (n - 1)))⁻¹ ((q : ℝ) ^ (n - 1) * M)⁻¹ (denom n ((q : ℂ) ^ (n - 1)) α) (fun X => ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) (by positivity) (differentiable_denom _ _ _) (by fun_prop …`. Conclude with `mul_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hP).1 i (Finset.mem_univ i))`.
-/
theorem trivialBound_of_bounded : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α w → (∃ C : ℝ, ∀ g, ‖w g‖ ≤ C) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  intro H L _ _ _ ϖ σ q n hU α w hw hb
  obtain ⟨C, hC⟩ := hb
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  obtain ⟨deg, hdeg⟩ := exists_deg ϖ hU (by omega : 1 ≤ n)
  letI : MeasurableSpace (GU σ n) := borel _
  haveI : BorelSpace (GU σ n) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L (ϖ : L) σ q n hU).1
  have hc1 : (1 : ℝ) ≤ (q : ℝ) ^ (n - 1) := one_le_pow₀ hq1
  have hc0 : (0 : ℝ) < (q : ℝ) ^ (n - 1) := by positivity
  have hny : ∀ x : ℝ, 0 < x → ‖(q : ℂ) ^ (n - 1) * (x : ℂ)‖ = (q : ℝ) ^ (n - 1) * x := fun x hx => by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hx.le]

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU n
  have hb0 := (trivialBound_iff (by omega) (by omega) α0).1 (GlobalTheory.ZetaSumU.tb_triv q n hq2 α0 hα0)
  have hsum : ∀ r : ℝ, 0 < r → r < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ → Summable fun a => r ^ deg a := fun r hr hρ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, -, hY, hinv, hval⟩ := hdeg (r : ℂ) (by exact_mod_cast hr.ne')
    have hdom : Domain (varY q (χ ϖ) s) α0 := by
      rw [hY]
      refine domain_of_bound hc1 hb0 ?_
      rw [hny r hr, mul_right_comm, ← pow_add, ← two_mul]
      exact (mul_lt_mul_of_pos_left hρ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    have hint := ((H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α0 _ hw0).1 hdom).1
    have hs := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ (fun g k hk => by simp only [hinv g k hk]) hint
    refine hs.congr fun a => ?_
    simp only [hval, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]

  obtain ⟨M, hM, hαM⟩ := exists_bound α
  have heq : ∀ x : ℝ, 0 < x → x < ((q : ℝ) ^ (n - 1) * M)⁻¹ →
      (∑' a : GU σ n ⧸ KU σ n, w a.out * (x : ℂ) ^ deg a) * denom n ((q : ℂ) ^ (n - 1)) α x =
        ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * (x : ℂ)) := fun x hx hδ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, hX, hY, hinv, hval⟩ := hdeg (x : ℂ) (by exact_mod_cast hx.ne')
    have hdom : Domain ((q : ℂ) ^ (n - 1) * (x : ℂ)) α := by
      refine domain_of_bound hM hαM ?_
      rw [hny x hx, mul_right_comm]
      exact (mul_lt_mul_of_pos_left hδ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    obtain ⟨hint, hI, -⟩ := (H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α w hw).1 (by rw [hY]; exact hdom)
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) * w (g * k) = Φ (io1 σ n g) * w g := fun g k hk => by
      have h1 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h1
      rw [hinv g k hk, h1]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK (fun g => Φ (io1 σ n g) * w g) _ hF hs.hasSum).2
    rw [hI, hX, hY] at hci
    rw [← closedForm_mul_denom q n _ _ α hdom, hci]
    congr 1
    exact tsum_congr fun a => by rw [hval, mul_comm]
  refine trivialBound_of_ne_zero (by omega) α fun i X hX => ?_
  have hP := GlobalTheory.gradedSeries_mul_ne_zero (GU σ n ⧸ KU σ n) deg (fun a => w a.out) ((q : ℝ) ^ (2 * (n - 1)))⁻¹
    ((q : ℝ) ^ (n - 1) * M)⁻¹ (denom n ((q : ℂ) ^ (n - 1)) α)
    (fun X => ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) (by positivity) (differentiable_denom _ _ _)
    (by fun_prop)
    (fun r hr hρ => Summable.of_nonneg_of_le (fun a => by positivity)
      (fun a => mul_le_mul_of_nonneg_right (hC _) (by positivity)) ((hsum r hr hρ).mul_left C))
    heq X hX (numer_ne_zero (by omega) hX)
  exact mul_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hP).1 i (Finset.mem_univ i))

end GlobalTheory.ZonalBound

end
