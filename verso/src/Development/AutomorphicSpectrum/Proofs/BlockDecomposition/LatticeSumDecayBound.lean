import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiDimensional
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Count

/- English proof (translation)
Establish `h1 : 0 < b + x` using `by linarith`. Establish `h2 : 0 < b + x + 1` using `by linarith`. Establish `e1 : (1 + (x + 1) / b) = (b + x + 1) / b` using `by field_simp; ring`. Establish `e2 : b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) = b ^ 2 / ((b + x) * (b + x + 1))` using `by field_simp; ring`. Rewrite using `[e1, e2, div_pow, inv_div]`.

Apply `div_le_div_of_nonneg_left (by positivity) (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_dim_step (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ((1 + (x + 1) / b) ^ 2)⁻¹ ≤ b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) := by
  have h1 : 0 < b + x := by linarith
  have h2 : 0 < b + x + 1 := by linarith
  have e1 : (1 + (x + 1) / b) = (b + x + 1) / b := by field_simp; ring
  have e2 : b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) = b ^ 2 / ((b + x) * (b + x + 1)) := by
    field_simp; ring
  rw [e1, e2, div_pow, inv_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Establish `: b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b`. Simplify using `only [Nat.cast_zero, add_zero]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Finset.range_zero, Finset.sum_empty, this, sub_self]`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_range_succ]`. Use `one_dim_step b N hb (Nat.cast_nonneg N)` as an intermediate fact. Use `push_cast`.

Establish `e : b + ((N : ℝ) + 1) = b + N + 1` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_dim_partial (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹ ≤ b - b ^ 2 / (b + N) := by
  induction N with
  | zero =>
    have : b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b := by
      simp only [Nat.cast_zero, add_zero]; field_simp
    rw [Finset.range_zero, Finset.sum_empty, this, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := one_dim_step b N hb (Nat.cast_nonneg N)
    push_cast
    have e : b + ((N : ℝ) + 1) = b + N + 1 := by ring
    rw [e]
    linarith

/- English proof (translation)
Rewrite using `[ENNReal.tsum_eq_iSup_nat]`. Use `iSup_le fun N => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Use `one_dim_partial b hb N` as an intermediate fact.

Establish `h3 : 0 ≤ b ^ 2 / (b + N)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_dim_nat (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹) ≤ ENNReal.ofReal b := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := one_dim_partial b hb N
  have h3 : 0 ≤ b ^ 2 / (b + N) := by positivity
  linarith

/- English proof (translation)
Use `set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf`. Establish `hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1)))` using `HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum`. Establish `hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) = ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹)`. Introduce `n`. Establish `: |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1`.

Use `push_cast`. Rewrite using `[abs_neg, abs_of_nonneg (by positivity)]`. Simplify using `only [hf, this]`. Establish `hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) = ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹)`. Introduce `n`.

Establish `: |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1`. Use `push_cast`. Rewrite using `[abs_of_nonneg (by positivity)]`. Simplify using `only [hf, this]`. Establish `h0 : f ((0 : ℕ) : ℤ) = 1` using `by simp [hf]`.

Establish `hN` using `one_dim_nat b hb`. Establish `hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b`. Rewrite using `[ENNReal.tsum_eq_iSup_nat]`. Use `iSup_le fun N => ?_` and prove the remaining obligations. Consider the cases of `N with`.

Consider the case `zero => simp`. Consider the case `succ N`. Rewrite using `[Finset.sum_range_succ', h0, add_comm]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hsplit.tsum_eq, tsum_congr hneg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le, ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]`.
-/
theorem one_dim (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf
  have hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have h0 : f ((0 : ℕ) : ℤ) = 1 := by simp [hf]
  have hN := one_dim_nat b hb
  have hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', h0, add_comm]
      gcongr
      calc ∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℤ)
          ≤ ∑' k : ℕ, f ((k + 1 : ℕ) : ℤ) := ENNReal.sum_le_tsum _
        _ ≤ ENNReal.ofReal b := by rw [tsum_congr hpos]; exact hN
  rw [hsplit.tsum_eq, tsum_congr hneg]
  calc _ ≤ 1 + ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hz hN
    _ = ENNReal.ofReal (1 + 2 * b) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le,
        ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g`.
-/
theorem multi_dim {P : Type} [Fintype P] (g : P → ℤ → ℝ≥0∞) :
    ∑' x : P → ℤ, ∏ p, g p (x p) ≤ ∏ p, ∑' n, g p n :=
  _root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g

/- English proof (translation)
Use `set g : P → ℤ → ℝ≥0∞ := fun p n => ENNReal.ofReal (((1 + |(n : ℝ)| / b p) ^ 2)⁻¹) with hg`. Establish `hsupp : ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ` using `(tsum_subtype_eq_of_support_subset (f := h) (s := {ξ | h ξ ≠ 0}) (fun _ hx => hx)).symm`. Establish `hinj' : Function.Injective (fun ξ : {ξ | h ξ ≠ 0} => m ξ)` using `fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tsum_le_prod_of_injOn {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ)
    (hb : ∀ p, 0 < b p) (h : S → ℝ≥0∞) (hinj : Set.InjOn m {ξ | h ξ ≠ 0})
    (hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) :
    ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  set g : P → ℤ → ℝ≥0∞ := fun p n => ENNReal.ofReal (((1 + |(n : ℝ)| / b p) ^ 2)⁻¹) with hg
  have hsupp : ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ :=
    (tsum_subtype_eq_of_support_subset (f := h) (s := {ξ | h ξ ≠ 0})
      (fun _ hx => hx)).symm
  have hinj' : Function.Injective (fun ξ : {ξ | h ξ ≠ 0} => m ξ) :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  calc ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ := hsupp
    _ ≤ ∑' ξ : {ξ | h ξ ≠ 0}, (fun x : P → ℤ => ∏ p, g p (x p)) (m ξ) :=
        ENNReal.tsum_le_tsum fun ξ => hh ξ
    _ ≤ ∑' x : P → ℤ, ∏ p, g p (x p) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj' _
    _ ≤ ∏ p, ∑' n, g p n := multi_dim g
    _ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) :=
        Finset.prod_le_prod' fun p _ => one_dim (b p) (hb p)

end GlobalTheory.CompanionTheory.Count
