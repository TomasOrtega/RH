import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x5

open Finset Formalism.FourierDecayAlt.S3

/- English proof (translation)
Unfold `densP`. Apply `Finset.prod_eq_zero (i := (0 : ℤ)) (Finset.mem_Icc.2 ⟨h1, h2⟩)` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem densityProduct_eq_zero (η : ℤ) (q : ℕ) (lo hi : ℤ) (h1 : lo ≤ 0) (h2 : 0 ≤ hi) : densP η q lo hi = 0 := by
  unfold densP
  apply Finset.prod_eq_zero (i := (0 : ℤ)) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  simp

/- English proof (translation)
Unfold `densP`. Rewrite using `[← Finset.prod_union]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_union]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `i hi1 hi2`. Simplify using `only [Finset.mem_Icc] at hi1 hi2`. Use linear arithmetic over natural numbers and integers.
-/
theorem densityProduct_split (η : ℤ) (q : ℕ) (lo mid hi : ℤ) (h1 : lo ≤ mid + 1) (h2 : mid ≤ hi) :
    densP η q lo hi = densP η q lo mid * densP η q (mid + 1) hi := by
  unfold densP
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  · rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_Icc] at hi1 hi2
    omega

/- English proof (translation)
Establish `hq' : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `h1 : (q : ℝ) ^ (-i) ≤ (q : ℝ) ^ (-1 : ℤ)` using `zpow_le_zpow_right₀ (by linarith) (by omega)`. Establish `h2 : (q : ℝ) ^ (-1 : ℤ) ≤ 1 / 2`. Rewrite using `[zpow_neg_one, one_div]`. Conclude with `inv_anti₀ (by norm_num) hq'`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem qpow_le_half (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) : (q : ℝ) ^ (-i) ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (-i) ≤ (q : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have h2 : (q : ℝ) ^ (-1 : ℤ) ≤ 1 / 2 := by
    rw [zpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hq'
  linarith

/- English proof (translation)
Break down `hη with rfl | rfl` into its components or cases. Use `left`. Simplify using the standard rewrite rules. Break down `Int.even_or_odd i with h | h` into its components or cases. Use `left`.

Use `push_cast`. Conclude with `h.neg_one_zpow`. Use `right`. Use `push_cast`. Conclude with `h.neg_one_zpow`.
-/
theorem eta_pow (η : ℤ) (hη : η = 1 ∨ η = -1) (i : ℤ) : ((η : ℝ) ^ i = 1 ∨ (η : ℝ) ^ i = -1) := by
  rcases hη with rfl | rfl
  · left; simp
  · rcases Int.even_or_odd i with h | h
    · left; push_cast; exact h.neg_one_zpow
    · right; push_cast; exact h.neg_one_zpow

/- English proof (translation)
Establish `hpos : 0 < (q : ℝ) ^ (-i)` using `zpow_pos (by exact_mod_cast (by omega : 0 < q)) _`. Apply the tactic sequence `rcases eta_pow η hη i with h | h <;> rw [h] <;> constructor <;> linarith`.
-/
theorem factor_bounds (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (_hi : 1 ≤ i) :
    1 - (q : ℝ) ^ (-i) ≤ 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ∧
      1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ≤ 1 + (q : ℝ) ^ (-i) := by
  have hpos : 0 < (q : ℝ) ^ (-i) := zpow_pos (by exact_mod_cast (by omega : 0 < q)) _
  rcases eta_pow η hη i with h | h <;> rw [h] <;> constructor <;> linarith

/- English proof (translation)
Use `(factor_bounds η hη q hq i hi).1` as an intermediate fact. Use `qpow_le_half q hq i hi` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem factor_pos (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) :
    0 < 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) := by
  have := (factor_bounds η hη q hq i hi).1
  have := qpow_le_half q hq i hi
  linarith

/- English proof (translation)
Unfold `densP`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i hi'`. Conclude with `factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)`.
-/
theorem densityProduct_pos (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    0 < densP η q lo hi := by
  unfold densP
  apply Finset.prod_pos
  intro i hi'
  exact factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)

/- English proof (translation)
Establish `hq' : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Break down `lt_or_ge b a with h | h` into its components or cases. Rewrite using `[Finset.Icc_eq_empty (by omega)]`. Simplify using `only [Finset.sum_empty]`.

Check the signs of the components of the expression. Establish `key : ∀ b : ℤ, a ≤ b → ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) + (q : ℝ) ^ (-b) ≤ 2 * (q : ℝ) ^ (-a)`. Introduce `b hb`. Proceed by induction on `b, hb using Int.leInduction with`. Consider the case `base => simp`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ b hb ih`. Establish `e : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b)`. Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Finset.sum_insert (by simp)]`. Establish `e2 : (q : ℝ) ^ (-b) = (q : ℝ) ^ (-(b + 1)) * q`. Rewrite using `[← zpow_add_one₀ hq0.ne']`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hp : 0 < (q : ℝ) ^ (-(b + 1))` using `zpow_pos hq0 _`. Use the polynomial consequences of the given equalities and inequalities. Use `key b h` as an intermediate fact. Establish `hp : 0 < (q : ℝ) ^ (-b)` using `zpow_pos hq0 _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geom_le (q : ℕ) (hq : 2 ≤ q) (a b : ℤ) :
    ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) ≤ 2 * (q : ℝ) ^ (-a) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  rcases lt_or_ge b a with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have key : ∀ b : ℤ, a ≤ b →
        ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) + (q : ℝ) ^ (-b) ≤ 2 * (q : ℝ) ^ (-a) := by
      intro b hb
      induction b, hb using Int.leInduction with
      | base => simp; linarith
      | succ b hb ih =>
        have e : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [e, Finset.sum_insert (by simp)]
        have e2 : (q : ℝ) ^ (-b) = (q : ℝ) ^ (-(b + 1)) * q := by
          rw [← zpow_add_one₀ hq0.ne']; congr 1; ring
        have hp : 0 < (q : ℝ) ^ (-(b + 1)) := zpow_pos hq0 _
        nlinarith
    have := key b h
    have hp : 0 < (q : ℝ) ^ (-b) := zpow_pos hq0 _
    linarith

/- English proof (translation)
Unfold `densP`. Rewrite using `[Real.exp_sum]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i hi'`. Conclude with `(factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).le`.

Introduce `i hi'`. Establish `h1` using `(factor_bounds η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).2`. Establish `h2` using `Real.add_one_le_exp ((q : ℝ) ^ (-i))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem densityProduct_le_exp (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    densP η q lo hi ≤ Real.exp (∑ i ∈ Finset.Icc lo hi, (q : ℝ) ^ (-i)) := by
  unfold densP
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi'
    exact (factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).le
  · intro i hi'
    have h1 := (factor_bounds η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).2
    have h2 := Real.add_one_le_exp ((q : ℝ) ^ (-i))
    linarith

/- English proof (translation)
Establish `h2 : 1 + 2 * x ≤ Real.exp (2 * x)` using `by have := Real.add_one_le_exp (2 * x); linarith`. Establish `h3 : (1 - x)⁻¹ ≤ 1 + 2 * x`. Rewrite using `[inv_le_iff_one_le_mul₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h2 : 1 + 2 * x ≤ Real.exp (2 * x) := by have := Real.add_one_le_exp (2 * x); linarith
  have h3 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  linarith

/- English proof (translation)
Unfold `densP`. Rewrite using `[Real.exp_sum, ← Finset.prod_inv_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i hi'`. Conclude with `(inv_pos.2 (factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega))).le`.

Introduce `i hi'`. Establish `hi1 : 1 ≤ i` using `by have := (Finset.mem_Icc.1 hi').1; omega`. Establish `h1` using `(factor_bounds η hη q hq i hi1).1`. Establish `h2` using `qpow_le_half q hq i hi1`. Establish `hpos : 0 < (q : ℝ) ^ (-i)` using `zpow_pos (by exact_mod_cast (by omega : 0 < q)) _`.

Establish `h3` using `inv_one_sub_le _ hpos.le h2`. Establish `h4 : (1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i))⁻¹ ≤ (1 - (q : ℝ) ^ (-i))⁻¹` using `inv_anti₀ (by linarith) h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem densityProduct_inv_le_exp (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    (densP η q lo hi)⁻¹ ≤ Real.exp (∑ i ∈ Finset.Icc lo hi, 2 * (q : ℝ) ^ (-i)) := by
  unfold densP
  rw [Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro i hi'
    exact (inv_pos.2 (factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega))).le
  · intro i hi'
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.1 hi').1; omega
    have h1 := (factor_bounds η hη q hq i hi1).1
    have h2 := qpow_le_half q hq i hi1
    have hpos : 0 < (q : ℝ) ^ (-i) := zpow_pos (by exact_mod_cast (by omega : 0 < q)) _
    have h3 := inv_one_sub_le _ hpos.le h2
    have h4 : (1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i))⁻¹ ≤ (1 - (q : ℝ) ^ (-i))⁻¹ :=
      inv_anti₀ (by linarith) h1
    linarith

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5

/- English proof (translation)
Introduce `η q k r c`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> push_cast <;> ring`.
-/
theorem density_case_split : Formalism.FourierDecayAlt.S3.DensCases := by
  intro η q k r c
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> push_cast <;> ring

/- English proof (translation)
Introduce `g r hg`. Rewrite using `[← zpow_natCast (g ^ (-3 : ℤ)) (r + 1), ← _root_.zpow_mul, ← zpow_add₀ hg.ne', ← zpow_sub₀ hg.ne', one_div, ← _root_.zpow_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem typed_unit_verification : Formalism.FourierDecayAlt.S3.TypedUnitCheck := by
  intro g r hg
  rw [← zpow_natCast (g ^ (-3 : ℤ)) (r + 1), ← _root_.zpow_mul, ← zpow_add₀ hg.ne', ← zpow_sub₀ hg.ne',
    one_div, ← _root_.zpow_neg]
  congr 1; push_cast; ring

/- English proof (translation)
Introduce `η q k r c l l' hη hq hk hc hl hl'`. Establish `hq' : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Use `set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn`. Establish `hnk : n = (k : ℤ) + 2 * r + 1` using `by rw [hn]; push_cast; ring`.

Break down `le_or_gt ((k : ℤ) - c) 0 with h0 | h0` into its components or cases. Rewrite using `[densityProduct_eq_zero η q _ _ h0 (by omega), zero_div]`. Conclude with `(Real.exp_pos _).le`. Apply the tactic sequence `have hlk : (k : ℤ) ≤ l ∧ (l : ℤ) ≤ k + 1 := by rcases hl with rfl | rfl <;> constructor <;> push_cast <;> omega`. Establish `hlk' : (k : ℤ) ≤ l' ∧ (l' : ℤ) ≤ k + 1`.

Apply the tactic sequence `rcases hl' with rfl | rfl <;> constructor <;> push_cast <;> omega`. Establish `hs` using `densityProduct_split η q ((k : ℤ) - c) ((l : ℤ) - 1) n (by omega) (by omega)`. Rewrite `hs` using `[sub_add_cancel]`. Establish `hP1 : 0 < densP η q l n` using `densityProduct_pos η hη q hq _ _ (by omega)`. Establish `hP2 : 0 < densP η q l' n` using `densityProduct_pos η hη q hq _ _ (by omega)`.

Establish `e : densP η q ((k : ℤ) - c) n / (densP η q l n * densP η q l' n) = densP η q ((k : ℤ) - c) ((l : ℤ) - 1) * (densP η q l' n)⁻¹`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `b1` using `densityProduct_le_exp η hη q hq ((k : ℤ) - c) ((l : ℤ) - 1) (by omega)`.

Establish `b2` using `densityProduct_inv_le_exp η hη q hq l' n (by omega)`. Establish `b3 : 0 ≤ densP η q ((k : ℤ) - c) ((l : ℤ) - 1)` using `(densityProduct_pos η hη q hq _ _ (by omega)).le`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Rewrite using `[← Finset.mul_sum]`.

Establish `g1` using `geom_le q hq ((k : ℤ) - c) ((l : ℤ) - 1)`. Establish `g2` using `geom_le q hq (l' : ℤ) n`. Establish `m1 : (q : ℝ) ^ (-((k : ℤ) - c)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2))` using `zpow_le_zpow_right₀ (by linarith) (by omega)`. Establish `m2 : (q : ℝ) ^ (-(l' : ℤ)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1)` using `zpow_le_zpow_right₀ (by linarith) (by omega)`. Establish `m3 : (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)) = (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) * q`.

Rewrite using `[← zpow_add_one₀ hq0.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hp : 0 < (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1)` using `zpow_pos hq0 _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem density_ordinary_bound : Formalism.FourierDecayAlt.S3.DensOrdinaryBound := by
  intro η q k r c l l' hη hq hk hc hl hl'
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn
  have hnk : n = (k : ℤ) + 2 * r + 1 := by rw [hn]; push_cast; ring
  rcases le_or_gt ((k : ℤ) - c) 0 with h0 | h0
  · rw [densityProduct_eq_zero η q _ _ h0 (by omega), zero_div]
    exact (Real.exp_pos _).le
  · have hlk : (k : ℤ) ≤ l ∧ (l : ℤ) ≤ k + 1 := by rcases hl with rfl | rfl <;> constructor <;> push_cast <;> omega
    have hlk' : (k : ℤ) ≤ l' ∧ (l' : ℤ) ≤ k + 1 := by
      rcases hl' with rfl | rfl <;> constructor <;> push_cast <;> omega
    have hs := densityProduct_split η q ((k : ℤ) - c) ((l : ℤ) - 1) n (by omega) (by omega)
    rw [sub_add_cancel] at hs
    have hP1 : 0 < densP η q l n := densityProduct_pos η hη q hq _ _ (by omega)
    have hP2 : 0 < densP η q l' n := densityProduct_pos η hη q hq _ _ (by omega)
    have e : densP η q ((k : ℤ) - c) n / (densP η q l n * densP η q l' n) =
        densP η q ((k : ℤ) - c) ((l : ℤ) - 1) * (densP η q l' n)⁻¹ := by
      rw [hs]; field_simp
    rw [e]
    have b1 := densityProduct_le_exp η hη q hq ((k : ℤ) - c) ((l : ℤ) - 1) (by omega)
    have b2 := densityProduct_inv_le_exp η hη q hq l' n (by omega)
    have b3 : 0 ≤ densP η q ((k : ℤ) - c) ((l : ℤ) - 1) := (densityProduct_pos η hη q hq _ _ (by omega)).le
    calc _ ≤ Real.exp (∑ i ∈ Finset.Icc ((k : ℤ) - c) ((l : ℤ) - 1), (q : ℝ) ^ (-i)) *
          Real.exp (∑ i ∈ Finset.Icc (l' : ℤ) n, 2 * (q : ℝ) ^ (-i)) :=
          mul_le_mul b1 b2 (inv_pos.2 hP2).le (Real.exp_pos _).le
      _ = Real.exp (∑ i ∈ Finset.Icc ((k : ℤ) - c) ((l : ℤ) - 1), (q : ℝ) ^ (-i) +
          ∑ i ∈ Finset.Icc (l' : ℤ) n, 2 * (q : ℝ) ^ (-i)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [← Finset.mul_sum]
        have g1 := geom_le q hq ((k : ℤ) - c) ((l : ℤ) - 1)
        have g2 := geom_le q hq (l' : ℤ) n
        have m1 : (q : ℝ) ^ (-((k : ℤ) - c)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)) :=
          zpow_le_zpow_right₀ (by linarith) (by omega)
        have m2 : (q : ℝ) ^ (-(l' : ℤ)) ≤ (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) :=
          zpow_le_zpow_right₀ (by linarith) (by omega)
        have m3 : (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)) = (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) * q := by
          rw [← zpow_add_one₀ hq0.ne']; congr 1; ring
        have hp : 0 < (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2) - 1) := zpow_pos hq0 _
        nlinarith

/- English proof (translation)
Introduce `g k r c hg`. Establish `hg' : (2 : ℝ) ≤ g` using `by exact_mod_cast hg`. Establish `hg0 : (0 : ℝ) < g` using `by linarith`. Use `set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn`. Establish `hnk : n = (k : ℤ) + 2 * r + 1` using `by rw [hn]; push_cast; ring`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hs` using `densityProduct_split 1 g ((k : ℤ) - c) k n (by omega) (by omega)`. Establish `hP : 0 < densP 1 g ((k : ℤ) + 1) n` using `densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)`. Rewrite using `[hs]`. Establish `e : (g : ℝ) ^ (-(2 * ((r : ℤ) + 1) * ((k : ℤ) - 1))) * (g : ℝ) ^ (-(3 * ((r : ℤ) + 1) ^ 2)) = (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2))`.

Rewrite using `[← zpow_add₀ hg0.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : 0 < (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2))` using `zpow_pos hg0 _`. Rewrite using `[div_eq_iff (by positivity), ← e]`.

Expand and normalize the polynomial expressions, which then agree. Break down `le_or_gt ((k : ℤ) - c) 0 with h0 | h0` into its components or cases. Rewrite using `[densityProduct_eq_zero 1 g _ _ h0 (by omega)]`. Conclude with `⟨le_refl _, zero_le_one⟩`. Use `⟨(densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)).le, ?_⟩` and prove the remaining obligations.

Unfold `densP`. Apply `Finset.prod_le_one` to reduce the goal to its premises. Introduce `i hi`. Conclude with `(factor_pos 1 (Or.inl rfl) g hg i (by have := (Finset.mem_Icc.1 hi).1; omega)).le`. Introduce `i hi`.

Establish `hpos : 0 < (g : ℝ) ^ (-i)` using `zpow_pos hg0 _`. Simplify using `only [Int.cast_one, one_zpow, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem densTyped_statement : Formalism.FourierDecayAlt.S3.DensTyped := by
  intro g k r c hg
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  set n : ℤ := ((k + 2 * r + 1 : ℕ) : ℤ) with hn
  have hnk : n = (k : ℤ) + 2 * r + 1 := by rw [hn]; push_cast; ring
  refine ⟨?_, ?_⟩
  · have hs := densityProduct_split 1 g ((k : ℤ) - c) k n (by omega) (by omega)
    have hP : 0 < densP 1 g ((k : ℤ) + 1) n := densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)
    rw [hs]
    have e : (g : ℝ) ^ (-(2 * ((r : ℤ) + 1) * ((k : ℤ) - 1))) * (g : ℝ) ^ (-(3 * ((r : ℤ) + 1) ^ 2)) =
        (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2)) := by
      rw [← zpow_add₀ hg0.ne']; congr 1; ring
    have hz : 0 < (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2)) :=
      zpow_pos hg0 _
    rw [div_eq_iff (by positivity), ← e]
    ring
  · rcases le_or_gt ((k : ℤ) - c) 0 with h0 | h0
    · rw [densityProduct_eq_zero 1 g _ _ h0 (by omega)]
      exact ⟨le_refl _, zero_le_one⟩
    · refine ⟨(densityProduct_pos 1 (Or.inl rfl) g hg _ _ (by omega)).le, ?_⟩
      unfold densP
      apply Finset.prod_le_one
      · intro i hi
        exact (factor_pos 1 (Or.inl rfl) g hg i (by have := (Finset.mem_Icc.1 hi).1; omega)).le
      · intro i hi
        have hpos : 0 < (g : ℝ) ^ (-i) := zpow_pos hg0 _
        simp only [Int.cast_one, one_zpow, one_mul]
        linarith

/- English proof (translation)
Introduce `s N hs`. Establish `key : ∀ N : ℕ, 2 ≤ N → ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - 1 / N`. Introduce `N hN`. Proceed by induction on `N, hN using Nat.le_induction with`. Consider the case `base => norm_num`.

Consider the case `succ N hN ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `: (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ)`. Use `push_cast`.

Rewrite using `[div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key2 : ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4`. Break down `lt_or_ge N 2 with h | h` into its components or cases.

Rewrite using `[Finset.Icc_eq_empty (by omega)]; norm_num`. Use `key N h` as an intermediate fact. Establish `: (0 : ℝ) ≤ 1 / N` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨t, rfl⟩ : ∃ t, s = 2 + t` from `⟨s - 2, by omega⟩`.

Establish `h1 : ∀ l ∈ Icc 2 N, ((l : ℝ) ^ (2 + t))⁻¹ ≤ ((l : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ t)⁻¹`. Introduce `l hl`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast (Finset.mem_Icc.1 hl).1`. Rewrite using `[pow_add, mul_inv]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Conclude with `inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hl2 t)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prime_tail_bound : Formalism.FourierDecayAlt.S3.PrimeTail := by
  intro s N hs
  have key : ∀ N : ℕ, 2 ≤ N → ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - 1 / N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have : (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have key2 : ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4 := by
    rcases lt_or_ge N 2 with h | h
    · rw [Finset.Icc_eq_empty (by omega)]; norm_num
    · have := key N h
      have : (0 : ℝ) ≤ 1 / N := by positivity
      linarith
  obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
  have h1 : ∀ l ∈ Icc 2 N, ((l : ℝ) ^ (2 + t))⁻¹ ≤ ((l : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ t)⁻¹ := by
    intro l hl
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    rw [pow_add, mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hl2 t)
  calc _ ≤ ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ t)⁻¹ := Finset.sum_le_sum h1
    _ = (∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹) * ((2 : ℝ) ^ t)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ 3 / 4 * ((2 : ℝ) ^ t)⁻¹ := mul_le_mul_of_nonneg_right key2 (by positivity)
    _ = _ := by rw [pow_add, mul_inv]; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Polynomial Formalism.FourierDecayAlt.S3

@[reducible] def starRingOfCard (K : Type) [Field K] [Fintype K] (q : ℕ) (hc : Fintype.card K = q ^ 2) :
    StarRing K where
  star x := x ^ q
  star_involutive x := by
    show (x ^ q) ^ q = x
    rw [← pow_mul, ← sq, ← hc, FiniteField.pow_card]
  star_mul x y := by
    show (x * y) ^ q = y ^ q * x ^ q
    rw [mul_pow, mul_comm]
  star_add x y := by
    show (x + y) ^ q = x ^ q + y ^ q
    obtain ⟨p, hp⟩ := CharP.exists K
    obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
    have : Fact p.Prime := ⟨hpp⟩
    have hd : q ∣ p ^ (n : ℕ) := by rw [← hn, hc]; exact dvd_pow_self q (by norm_num)
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hpp).1 hd
    exact add_pow_char_pow x y p m

variable {K : Type} [Field K] [Fintype K]

/- English proof (translation)
Establish `h` using `Fintype.one_lt_card (α := K)`. Rewrite `h` using `[hc]`. Assume the negation of the conclusion as `hq`. Establish `: q = 0 ∨ q = 1` using `by omega`. Apply the tactic sequence `rcases this with rfl | rfl <;> norm_num at h`.
-/
theorem two_le_q {q : ℕ} (hc : Fintype.card K = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := K)
  rw [hc] at h
  by_contra hq
  have : q = 0 ∨ q = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Combine the equalities or inequalities in the displayed calculation. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx`. Simplify using `only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]`.

Conclude with `hx)`. Use `_ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _`. Use `_ ≤ _ := Polynomial.card_roots' p`.
-/
theorem card_root_le (p : K[X]) (hp : p ≠ 0) : Nat.card {x : K // p.eval x = 0} ≤ p.natDegree := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc _ ≤ p.roots.toFinset.card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
        exact hx)
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ _ := Polynomial.card_roots' p

/- English proof (translation)
Establish `hdeg : (C e * X : K[X]).degree < (q : ℕ)`. Combine the equalities or inequalities in the displayed calculation. Use `(Polynomial.degree_C_mul_X_le e)` and prove the remaining obligations. Use `_ < (q : ℕ) := by exact_mod_cast (by omega : 1 < q)`. Establish `hm : (X ^ q + C e * X : K[X]).Monic` using `Polynomial.monic_X_pow_add hdeg`.

Establish `hn : (X ^ q + C e * X : K[X]).natDegree = q`. Establish `: (X ^ q + C e * X : K[X]).degree = (q : ℕ)`. Rewrite using `[Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]`. Conclude with `Polynomial.natDegree_eq_of_degree_eq_some this`. Use `card_root_le _ hm.ne_zero` as an intermediate fact.

Rewrite `this` using `[hn]`. Simplify using `using this`.
-/
theorem card_pm_le {q : ℕ} (hq : 2 ≤ q) (e : K) : Nat.card {x : K // x ^ q + e * x = 0} ≤ q := by
  have hdeg : (C e * X : K[X]).degree < (q : ℕ) := by
    calc (C e * X : K[X]).degree ≤ 1 := by
          refine (Polynomial.degree_C_mul_X_le e)
      _ < (q : ℕ) := by exact_mod_cast (by omega : 1 < q)
  have hm : (X ^ q + C e * X : K[X]).Monic := Polynomial.monic_X_pow_add hdeg
  have hn : (X ^ q + C e * X : K[X]).natDegree = q := by
    have : (X ^ q + C e * X : K[X]).degree = (q : ℕ) := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  have := card_root_le _ hm.ne_zero
  rw [hn] at this
  simpa using this

variable [StarRing K]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[fconj, hs, Matrix.conjTranspose_apply]`.
-/
theorem fconj_eq {q : ℕ} (hs : ∀ x : K, star x = x ^ q) {m n : Type} (X : Matrix m n K) :
    fconj q X = Xᴴ := by
  ext i j
  simp [fconj, hs, Matrix.conjTranspose_apply]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Establish `hq` using `two_le_q hc`. Establish `h1` using `card_pm_le (K := K) hq 1`. Establish `h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card K`.

Apply `Nat.card_congr` to reduce the goal to its premises. Conclude with `Equiv.subtypeUnivEquiv (fun x => by have := hcon x; rw [hs] at this; rw [one_mul, add_comm]; exact this)`. Rewrite `h1` using `[h2, Nat.card_eq_fintype_card, hc]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_trace_ne {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) :
    ∃ μ : K, μ + star μ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hq := two_le_q hc
  have h1 := card_pm_le (K := K) hq 1
  have h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card K := by
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv (fun x => by have := hcon x; rw [hs] at this; rw [one_mul, add_comm]; exact this)
  rw [h2, Nat.card_eq_fintype_card, hc] at h1
  nlinarith

/- English proof (translation)
Establish `hq` using `two_le_q hc`. Establish `hfix : Nat.card {d : K // star d = d} ≤ q`. Establish `h1` using `card_pm_le (K := K) hq (-1)`. Establish `h2 : Nat.card {x : K // x ^ q + (-1) * x = 0} = Nat.card {d : K // star d = d}` using `Nat.card_congr (Equiv.subtypeEquivRight (fun x => by`. Rewrite using `[hs, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]))`.

Use linear arithmetic over natural numbers and integers. Set `Tr : K →+ K` to `AddMonoidHom.mk' (fun x => x + star x) (by intro a b; simp only [star_add]; ring)`. Establish `hker : Nat.card Tr.ker ≤ q`. Establish `h1` using `card_pm_le (K := K) hq 1`. Establish `h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card Tr.ker` using `Nat.card_congr (Equiv.subtypeEquivRight (fun x => by`.

Rewrite using `[AddMonoidHom.mem_ker]`. Use `show _ ↔ x + star x = 0`. Rewrite using `[hs, one_mul, add_comm]))`. Use linear arithmetic over natural numbers and integers. Establish `hrange : Nat.card Tr.range ≤ Nat.card {d : K // star d = d}`.

Apply `Nat.card_le_card_of_injective (fun y : Tr.range => (⟨y.1, by` to reduce the goal to its premises. Take `⟨x, hx⟩` from `y.2`. Rewrite using `[← hx]`. Use `show star (x + star x) = x + star x`. Rewrite using `[star_add, star_star, add_comm]⟩ : {d : K // star d = d}))`.

Introduce `y y' h`. Establish `h' : (y : K) = (y' : K)` using `congrArg (fun z : {d : K // star d = d} => z.1) h`. Conclude with `Subtype.ext h'`. Establish `hmul : Nat.card Tr.ker * Nat.card Tr.range = q ^ 2`. Rewrite using `[← AddSubgroup.index_ker, AddSubgroup.card_mul_index, Nat.card_eq_fintype_card, hc]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem card_fix {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) :
    Nat.card {d : K // star d = d} = q := by
  have hq := two_le_q hc
  have hfix : Nat.card {d : K // star d = d} ≤ q := by
    have h1 := card_pm_le (K := K) hq (-1)
    have h2 : Nat.card {x : K // x ^ q + (-1) * x = 0} = Nat.card {d : K // star d = d} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [hs, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]))
    omega
  let Tr : K →+ K := AddMonoidHom.mk' (fun x => x + star x) (by intro a b; simp only [star_add]; ring)
  have hker : Nat.card Tr.ker ≤ q := by
    have h1 := card_pm_le (K := K) hq 1
    have h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card Tr.ker :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [AddMonoidHom.mem_ker]
        show _ ↔ x + star x = 0
        rw [hs, one_mul, add_comm]))
    omega
  have hrange : Nat.card Tr.range ≤ Nat.card {d : K // star d = d} := by
    apply Nat.card_le_card_of_injective
      (fun y : Tr.range => (⟨y.1, by
        obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        show star (x + star x) = x + star x
        rw [star_add, star_star, add_comm]⟩ : {d : K // star d = d}))
    intro y y' h
    have h' : (y : K) = (y' : K) := congrArg (fun z : {d : K // star d = d} => z.1) h
    exact Subtype.ext h'
  have hmul : Nat.card Tr.ker * Nat.card Tr.range = q ^ 2 := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, Nat.card_eq_fintype_card, hc]
  nlinarith

/- English proof (translation)
Establish `hq` using `two_le_q hc`. Establish `hcardU : Nat.card Kˣ = (q - 1) * (q + 1)`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_units, hc]`. Take `⟨s, rfl⟩ : ∃ s, q = s + 1` from `⟨q - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`.

Establish `: (s + 1) ^ 2 = s * (s + 1 + 1) + 1` using `by ring`. Use linear arithmetic over natural numbers and integers. Establish `h1 : Nat.card (powMonoidHom (q + 1) : Kˣ →* Kˣ).range = q - 1`. Rewrite using `[IsCyclic.card_powMonoidHom_range, hcardU, Nat.gcd_eq_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ (by omega)]`. Establish `h2 : Nat.card (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker = q - 1`.

Rewrite using `[IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right (Dvd.intro _ rfl)]`. Establish `hle : (powMonoidHom (q + 1) : Kˣ →* Kˣ).range ≤ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `only [powMonoidHom_apply]`.

Rewrite using `[← pow_mul, mul_comm, ← hcardU]`. Conclude with `pow_card_eq_one'`. Establish `heq` using `Subgroup.eq_of_le_of_card_ge hle (by rw [h1, h2])`. Establish `hmem : Units.mk0 t ht ∈ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker`. Rewrite using `[MonoidHom.mem_ker]`.

Simplify using `only [powMonoidHom_apply]`. Use `ext`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]`. Rewrite `hst` using `[hs]`. Establish `: t ^ (q - 1) * t = 1 * t`.

Rewrite using `[← pow_succ, one_mul, Nat.sub_add_cancel (by omega)]; exact hst`. Conclude with `mul_right_cancel₀ ht this`. Rewrite `hmem` using `[← heq]`. Take `⟨x, hx⟩` from `hmem`. Use `⟨(x : K), ?_⟩` and prove the remaining obligations.

Rewrite using `[hs, ← pow_succ]`. Use `congrArg Units.val hx` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_surj {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (t : K) (ht : t ≠ 0) (hst : star t = t) : ∃ l : K, star l * l = t := by
  classical
  have hq := two_le_q hc
  have hcardU : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hc]
    obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = s * (s + 1 + 1) + 1 := by ring
    omega
  have h1 : Nat.card (powMonoidHom (q + 1) : Kˣ →* Kˣ).range = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_range, hcardU, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ (by omega)]
  have h2 : Nat.card (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right (Dvd.intro _ rfl)]
  have hle : (powMonoidHom (q + 1) : Kˣ →* Kˣ).range ≤ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hcardU]
    exact pow_card_eq_one'
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h1, h2])
  have hmem : Units.mk0 t ht ∈ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [hs] at hst
    have : t ^ (q - 1) * t = 1 * t := by
      rw [← pow_succ, one_mul, Nat.sub_add_cancel (by omega)]; exact hst
    exact mul_right_cancel₀ ht this
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : K), ?_⟩
  rw [hs, ← pow_succ]
  have := congrArg Units.val hx
  simpa using this

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero]`. Establish `: Unique {D : Matrix (Fin 0) (Fin 0) K // Dᴴ = D}` using `⟨⟨⟨0, by simp⟩⟩, fun D => Subtype.ext (by ext i; exact i.elim0)⟩`. Conclude with `Nat.card_unique`.

Consider the case `succ c ih`. Set `F : ({A : Matrix (Fin c) (Fin c) K // Aᴴ = A} × (Fin c → K) × {d : K // star d = d}) → {D : Matrix (Fin (c + 1)) (Fin (c + 1)) K // Dᴴ = D}` to `fun x => ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.1.1 (Matrix.of fun i (_ : Fin 1) => x.2.1 i) (Matrix.of fun i (_ : Fin 1) => x.2.1 i)ᴴ (Matrix.of fun (_ _ : Fin 1) => x.2.2.1)), by`. Rewrite using `[Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose, x.1.2, Matrix.conjTranspose_conjTranspose]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply, x.2.2.2]⟩`. Establish `hF : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A, b, d⟩ ⟨A', b', d'⟩ h`. Establish `h1` using `(Matrix.reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val h)`.

Rewrite `h1` using `[Matrix.fromBlocks_inj]`. Take `⟨hA, hb, -, hd⟩` from `h1`. Establish `hb' : b = b'`. Use function extensionality and compare the values at `i`. Conclude with `congrFun (congrFun hb i) 0`.

Establish `hd' : d = d'` using `Subtype.ext (congrFun (congrFun hd 0) 0)`. Establish `hA' : A = A'` using `Subtype.ext hA`. Rewrite using `[hA', hb', hd']`. Introduce and unpack `⟨D, hD⟩ set D' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm D with hD'`. Establish `hDD : D = Matrix.reindex finSumFinEquiv finSumFinEquiv D'`.

Rewrite using `[hD', Equiv.apply_symm_apply]`. Establish `hH : D'ᴴ = D'`. Apply `(Matrix.reindex (finSumFinEquiv (m := c) (n := 1)) (finSumFinEquiv (m := c) (n := 1))).injective` to reduce the goal to its premises. Rewrite using `[← Matrix.conjTranspose_reindex, ← hDD, hD]`. Establish `hb` using `Matrix.fromBlocks_toBlocks D'`.

Rewrite `hH` using `[← hb, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_inj]`. Take `⟨h11, h21, h12, h22⟩` from `hH`. Use `⟨⟨⟨D'.toBlocks₁₁, h11⟩, fun i => D'.toBlocks₁₂ i 0, ⟨D'.toBlocks₂₂ 0 0, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun h22 0) 0` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`.

Apply `Subtype.ext show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = D` to reduce the goal to its premises. Rewrite using `[hDD]`. Use `congr 1`. Use `conv_rhs => rw [← hb]`. Establish `e12 : (Matrix.of fun i (_ : Fin 1) => D'.toBlocks₁₂ i 0) = D'.toBlocks₁₂`.

Use extensionality with `i j`. Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Establish `e22 : (Matrix.of fun (_ _ : Fin 1) => D'.toBlocks₂₂ 0 0) = D'.toBlocks₂₂`. Use extensionality with `i j`.

Rewrite using `[Subsingleton.elim j 0, Subsingleton.elim i 0]`. Both sides reduce to the same expression. Rewrite using `[e12, e22, h12]`. Rewrite using `[← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_prod, ih, card_fix hs hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hc, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_herm {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) (c : ℕ) :
    Nat.card {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} = q ^ (c ^ 2) := by
  induction c with
  | zero =>
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero]
    have : Unique {D : Matrix (Fin 0) (Fin 0) K // Dᴴ = D} :=
      ⟨⟨⟨0, by simp⟩⟩, fun D => Subtype.ext (by ext i; exact i.elim0)⟩
    exact Nat.card_unique
  | succ c ih =>
    let F : ({A : Matrix (Fin c) (Fin c) K // Aᴴ = A} × (Fin c → K) × {d : K // star d = d}) →
        {D : Matrix (Fin (c + 1)) (Fin (c + 1)) K // Dᴴ = D} := fun x =>
      ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks x.1.1 (Matrix.of fun i (_ : Fin 1) => x.2.1 i)
          (Matrix.of fun i (_ : Fin 1) => x.2.1 i)ᴴ (Matrix.of fun (_ _ : Fin 1) => x.2.2.1)), by
        rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose, x.1.2,
          Matrix.conjTranspose_conjTranspose]
        congr 2
        ext i j
        simp [Matrix.conjTranspose_apply, x.2.2.2]⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨A, b, d⟩ ⟨A', b', d'⟩ h
        have h1 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val h)
        rw [Matrix.fromBlocks_inj] at h1
        obtain ⟨hA, hb, -, hd⟩ := h1
        have hb' : b = b' := by
          funext i
          exact congrFun (congrFun hb i) 0
        have hd' : d = d' := Subtype.ext (congrFun (congrFun hd 0) 0)
        have hA' : A = A' := Subtype.ext hA
        rw [hA', hb', hd']
      · rintro ⟨D, hD⟩
        set D' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm D with hD'
        have hDD : D = Matrix.reindex finSumFinEquiv finSumFinEquiv D' := by
          rw [hD', Equiv.apply_symm_apply]
        have hH : D'ᴴ = D' := by
          apply (Matrix.reindex (finSumFinEquiv (m := c) (n := 1)) (finSumFinEquiv (m := c) (n := 1))).injective
          rw [← Matrix.conjTranspose_reindex, ← hDD, hD]
        have hb := Matrix.fromBlocks_toBlocks D'
        rw [← hb, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_inj] at hH
        obtain ⟨h11, h21, h12, h22⟩ := hH
        refine ⟨⟨⟨D'.toBlocks₁₁, h11⟩, fun i => D'.toBlocks₁₂ i 0, ⟨D'.toBlocks₂₂ 0 0, ?_⟩⟩, ?_⟩
        · have := congrFun (congrFun h22 0) 0
          simpa [Matrix.conjTranspose_apply] using this
        · apply Subtype.ext
          show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = D
          rw [hDD]
          congr 1
          conv_rhs => rw [← hb]
          have e12 : (Matrix.of fun i (_ : Fin 1) => D'.toBlocks₁₂ i 0) = D'.toBlocks₁₂ := by
            ext i j; rw [Subsingleton.elim j 0]; rfl
          have e22 : (Matrix.of fun (_ _ : Fin 1) => D'.toBlocks₂₂ 0 0) = D'.toBlocks₂₂ := by
            ext i j; rw [Subsingleton.elim j 0, Subsingleton.elim i 0]; rfl
          rw [e12, e22, h12]
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_prod, ih, card_fix hs hc, Nat.card_fun,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hc, Fintype.card_fin]
    ring

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix

variable {K : Type} [Field K] [Fintype K] [StarRing K]

/- English proof (translation)
Introduce `u hu v hv`. Take `⟨μ, hμ⟩` from `htr`. Assume the negation of the conclusion as `hne`. Establish `hz0 : (uᴴ * J * v) () () ≠ 0`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `h`. Establish `hvu : vᴴ * J * u = (uᴴ * J * v)ᴴ`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`.

Establish `h1` using `h0 (u + (μ / (uᴴ * J * v) () ()) • v) (W.add_mem hu (W.smul_mem _ hv))`. Simplify using `only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h0 u hu, h0 v hv, hvu] at h1`. Establish `h2` using `congrFun (congrFun h1 ()) ()`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, conjTranspose_apply, smul_eq_mul, zero_add, mul_zero, add_zero] at h2`. Apply `hμ` to reduce the goal to its premises.

Rewrite `h2` using `[← star_mul', div_mul_cancel₀ _ hz0]`. Rewrite using `[add_comm]`. Conclude with `h2`.
-/
theorem polar (htr : ∃ μ : K, μ + star μ ≠ 0) {ν : Type} [Fintype ν] [DecidableEq ν]
    (J : Matrix ν ν K) (hJ : Jᴴ = J) (W : Submodule K (Matrix ν Unit K))
    (h0 : ∀ v ∈ W, vᴴ * J * v = 0) : ∀ u ∈ W, ∀ v ∈ W, uᴴ * J * v = 0 := by
  intro u hu v hv
  obtain ⟨μ, hμ⟩ := htr
  by_contra hne
  have hz0 : (uᴴ * J * v) () () ≠ 0 := by
    intro h
    apply hne
    ext i j
    exact h
  have hvu : vᴴ * J * u = (uᴴ * J * v)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have h1 := h0 (u + (μ / (uᴴ * J * v) () ()) • v) (W.add_mem hu (W.smul_mem _ hv))
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, h0 u hu, h0 v hv, hvu] at h1
  have h2 := congrFun (congrFun h1 ()) ()
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, conjTranspose_apply, smul_eq_mul,
    zero_add, mul_zero, add_zero] at h2
  apply hμ
  rw [← star_mul', div_mul_cancel₀ _ hz0] at h2
  rw [add_comm]
  exact h2

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem gram_submatrix {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (Z : Matrix ν α K) (e : β → α) :
    (Z.submatrix id e)ᴴ * J * (Z.submatrix id e) = (Zᴴ * J * Z).submatrix e e := by
  ext i j
  rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, by ext i; exact i.elim0⟩`. Consider the case `succ m ih`. Take `⟨X, hX⟩` from `ih (by omega)`. Set `f : Matrix ν Unit K →ₗ[K] Matrix (Fin m) Unit K` to `{ toFun := fun Y => Xᴴ * J * Y map_add' := fun a b => Matrix.mul_add _ _ _ map_smul' := fun c a => by simp }`.

Establish `hf : ∀ Y, f Y = Xᴴ * J * Y` using `fun _ => rfl`. Establish `hker : LinearMap.ker f ≠ ⊥`. Apply `LinearMap.ker_ne_bot_of_finrank_lt` to reduce the goal to its premises. Rewrite using `[Module.finrank_matrix, Module.finrank_matrix]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Take `⟨y, hyW, hy0⟩` from `(Submodule.ne_bot_iff _).1 hker`. Establish `hex : ∃ v ∈ LinearMap.ker f, vᴴ * J * v ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `hp` using `polar htr J hJ _ hcon`. Apply `hy0` to reduce the goal to its premises. Establish `hyX : Xᴴ * J * y = 0` using `by rw [← hf]; exact hyW`. Establish `hyJ : ∀ z : Matrix ν Unit K, yᴴ * J * z = 0`. Introduce `z`.

Establish `hz' : z - X * (Xᴴ * J * z) ∈ LinearMap.ker f`. Rewrite using `[LinearMap.mem_ker, hf, Matrix.mul_sub, ← Matrix.mul_assoc (Xᴴ * J) X, hX, Matrix.one_mul, sub_self]`. Establish `h1` using `hp y hyW _ hz'`. Establish `h2 : yᴴ * J * X = 0`. Establish `h3 : (Xᴴ * J * y)ᴴ = 0` using `by rw [hyX]; simp`.

Rewrite `h3` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Rewrite `h1` using `[Matrix.mul_sub, ← Matrix.mul_assoc (yᴴ * J) X, h2, Matrix.zero_mul, sub_zero]`. Conclude with `h1`. Establish `hyJ0 : yᴴ * J = 0`. Use extensionality with `a i`.

Establish `h4` using `congrFun (congrFun (hyJ (Matrix.single i () 1)) a) ()`. Simplify using `using h4`. Establish `hJy : J * y = 0`. Establish `h5` using `congrArg conjTranspose hyJ0`. Rewrite `h5` using `[conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_zero]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Take `⟨v, hvW, hv0⟩` from `hex`. Establish `hvX : Xᴴ * J * v = 0` using `by rw [← hf]; exact hvW`. Establish `ht0 : (vᴴ * J * v) () () ≠ 0`. Introduce `h`.

Apply `hv0` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `h`. Establish `hherm : (vᴴ * J * v)ᴴ = vᴴ * J * v`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`.

Establish `hst : star ((vᴴ * J * v) () ()) = (vᴴ * J * v) () ()`. Establish `h6` using `congrFun (congrFun hherm ()) ()`. Rewrite `h6` using `[conjTranspose_apply]`. Then use the resulting hypothesis. Take `⟨l, hl⟩` from `hnorm ((vᴴ * J * v) () ())⁻¹ (inv_ne_zero ht0) (by rw [star_inv₀, hst])`. Establish `hw1 : (l • v)ᴴ * J * (l • v) = 1`.

Use extensionality with `i j`. Simplify using `only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm l, hl, inv_mul_cancel₀ ht0]`. Simplify using the standard rewrite rules. Establish `hw2 : Xᴴ * J * (l • v) = 0` using `by rw [Matrix.mul_smul, hvX, smul_zero]`.

Establish `hw3 : (l • v)ᴴ * J * X = 0`. Establish `h3 : (Xᴴ * J * (l • v))ᴴ = 0` using `by rw [hw2]; simp`. Rewrite `h3` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Set `e : Fin m ⊕ Unit ≃ Fin (m + 1)` to `Fintype.equivOfCardEq (by simp)`. Use `⟨(Matrix.fromCols X (l • v)).submatrix id e.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[gram_submatrix, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, hX, hw1, hw2, hw3, fromBlocks_one, submatrix_one_equiv]`.
-/
theorem exists_frame (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {ν : Type} [Fintype ν] [DecidableEq ν] (J : Matrix ν ν K) (hJ : Jᴴ = J) (hd : IsUnit J.det)
    (m : ℕ) (hm : m ≤ Fintype.card ν) : ∃ X : Matrix ν (Fin m) K, Xᴴ * J * X = 1 := by
  induction m with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ m ih =>
    obtain ⟨X, hX⟩ := ih (by omega)
    let f : Matrix ν Unit K →ₗ[K] Matrix (Fin m) Unit K :=
      { toFun := fun Y => Xᴴ * J * Y
        map_add' := fun a b => Matrix.mul_add _ _ _
        map_smul' := fun c a => by simp }
    have hf : ∀ Y, f Y = Xᴴ * J * Y := fun _ => rfl
    have hker : LinearMap.ker f ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_matrix, Module.finrank_matrix]
      simp
      omega
    obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff _).1 hker
    have hex : ∃ v ∈ LinearMap.ker f, vᴴ * J * v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hp := polar htr J hJ _ hcon
      apply hy0
      have hyX : Xᴴ * J * y = 0 := by rw [← hf]; exact hyW
      have hyJ : ∀ z : Matrix ν Unit K, yᴴ * J * z = 0 := by
        intro z
        have hz' : z - X * (Xᴴ * J * z) ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf, Matrix.mul_sub, ← Matrix.mul_assoc (Xᴴ * J) X, hX, Matrix.one_mul,
            sub_self]
        have h1 := hp y hyW _ hz'
        have h2 : yᴴ * J * X = 0 := by
          have h3 : (Xᴴ * J * y)ᴴ = 0 := by rw [hyX]; simp
          rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
            ← Matrix.mul_assoc] at h3
        rw [Matrix.mul_sub, ← Matrix.mul_assoc (yᴴ * J) X, h2, Matrix.zero_mul, sub_zero] at h1
        exact h1
      have hyJ0 : yᴴ * J = 0 := by
        ext a i
        have h4 := congrFun (congrFun (hyJ (Matrix.single i () 1)) a) ()
        simpa using h4
      have hJy : J * y = 0 := by
        have h5 := congrArg conjTranspose hyJ0
        rwa [conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_zero] at h5
      calc y = J⁻¹ * (J * y) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = 0 := by rw [hJy, Matrix.mul_zero]
    obtain ⟨v, hvW, hv0⟩ := hex
    have hvX : Xᴴ * J * v = 0 := by rw [← hf]; exact hvW
    have ht0 : (vᴴ * J * v) () () ≠ 0 := by
      intro h
      apply hv0
      ext i j
      exact h
    have hherm : (vᴴ * J * v)ᴴ = vᴴ * J * v := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
    have hst : star ((vᴴ * J * v) () ()) = (vᴴ * J * v) () () := by
      have h6 := congrFun (congrFun hherm ()) ()
      rwa [conjTranspose_apply] at h6
    obtain ⟨l, hl⟩ := hnorm ((vᴴ * J * v) () ())⁻¹ (inv_ne_zero ht0) (by rw [star_inv₀, hst])
    have hw1 : (l • v)ᴴ * J * (l • v) = 1 := by
      ext i j
      simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm l, hl, inv_mul_cancel₀ ht0]
      simp
    have hw2 : Xᴴ * J * (l • v) = 0 := by rw [Matrix.mul_smul, hvX, smul_zero]
    have hw3 : (l • v)ᴴ * J * X = 0 := by
      have h3 : (Xᴴ * J * (l • v))ᴴ = 0 := by rw [hw2]; simp
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
        ← Matrix.mul_assoc] at h3
    let e : Fin m ⊕ Unit ≃ Fin (m + 1) := Fintype.equivOfCardEq (by simp)
    refine ⟨(Matrix.fromCols X (l • v)).submatrix id e.symm, ?_⟩
    rw [gram_submatrix, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      fromRows_mul_fromCols, hX, hw1, hw2, hw3, fromBlocks_one, submatrix_one_equiv]

/- English proof (translation)
Take `⟨X, hX⟩` from `exists_frame htr hnorm J hJ hdJ (Fintype.card μ) le_rfl`. Take `⟨Y, hY⟩` from `exists_frame htr hnorm D hD hdD (Fintype.card μ) hcard.le`. Establish `hX' : X * (Xᴴ * J) = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp)).1 hX`. Establish `hY' : Y * (Yᴴ * D) = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hcard])).1 hY`. Use `⟨X * (Yᴴ * D), Y * (Xᴴ * J), ?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hY, Matrix.mul_one, hX']`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hX, Matrix.mul_one, hY']`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hD, Matrix.mul_assoc]`. Use `_ = D * (Y * (Yᴴ * D)) := by rw [hX, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = D := by rw [hY', Matrix.mul_one]`.
-/
theorem exists_G (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (hcard : Fintype.card μ = Fintype.card ν) (J : Matrix μ μ K) (D : Matrix ν ν K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hD : Dᴴ = D) (hdD : IsUnit D.det) :
    ∃ (G : Matrix μ ν K) (G' : Matrix ν μ K), G * G' = 1 ∧ G' * G = 1 ∧ Gᴴ * J * G = D := by
  obtain ⟨X, hX⟩ := exists_frame htr hnorm J hJ hdJ (Fintype.card μ) le_rfl
  obtain ⟨Y, hY⟩ := exists_frame htr hnorm D hD hdD (Fintype.card μ) hcard.le
  have hX' : X * (Xᴴ * J) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp)).1 hX
  have hY' : Y * (Yᴴ * D) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hcard])).1 hY
  refine ⟨X * (Yᴴ * D), Y * (Xᴴ * J), ?_, ?_, ?_⟩
  · calc X * (Yᴴ * D) * (Y * (Xᴴ * J)) = X * (Yᴴ * D * Y) * (Xᴴ * J) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hX']
  · calc Y * (Xᴴ * J) * (X * (Yᴴ * D)) = Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hX, Matrix.mul_one, hY']
  · calc (X * (Yᴴ * D))ᴴ * J * (X * (Yᴴ * D)) = D * Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
      _ = D * (Y * (Yᴴ * D)) := by rw [hX, Matrix.mul_one, Matrix.mul_assoc]
      _ = D := by rw [hY', Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
/- English proof (translation)
Establish `h1` using `Matrix.mulVec_conjTranspose M u`. Rewrite `h1` using `[h]`. Establish `h2` using `congrArg star h1`. Simplify using `using h2.symm`.
-/
theorem star_vecMul_zero {α κ : Type} [Fintype α] (M : Matrix α κ K) (u : α → K)
    (h : Mᴴ *ᵥ u = 0) : star u ᵥ* M = 0 := by
  have h1 := Matrix.mulVec_conjTranspose M u
  rw [h] at h1
  have h2 := congrArg star h1
  simpa using h2.symm

omit [Fintype K] in
/- English proof (translation)
Take `⟨C, hC⟩` from `Submodule.exists_isCompl (LinearMap.range T.mulVecLin)`. Establish `hfin : Module.finrank K C = a - T.rank`. Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hC`. Rewrite `h1` using `[Module.finrank_fin_fun]`. Establish `h2 : Module.finrank K (LinearMap.range T.mulVecLin) = T.rank` using `rfl`.

Use linear arithmetic over natural numbers and integers. Set `b` to `Module.finBasisOfFinrankEq K C hfin`. Set `B : Matrix (Fin a) (Fin (a - T.rank)) K` to `Matrix.of fun i j => (b j : Fin a → K) i`. Establish `hBv : ∀ w : Fin (a - T.rank) → K, B *ᵥ w = ((∑ j, w j • b j : C) : Fin a → K)`. Introduce `w`.

Use extensionality with `i`. Simplify using `[B, Matrix.mulVec, dotProduct, mul_comm]`. Use `⟨B, fun D => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Establish `hker : ∀ x, (Matrix.fromBlocks T B Bᴴ D) *ᵥ x = 0 → x = 0`.

Introduce `x hx`. Rewrite `hx` using `[Matrix.fromBlocks_mulVec]`. Use `set u : Fin a → K := x ∘ Sum.inl with hu`. Use `set w : Fin (a - T.rank) → K := x ∘ Sum.inr with hw`. Establish `h1 : T *ᵥ u + B *ᵥ w = 0`.

Use function extensionality and compare the values at `i`. Use `congrFun hx (Sum.inl i)` as an intermediate fact. Simplify using `using this`. Establish `h2 : Bᴴ *ᵥ u + D *ᵥ w = 0`. Use function extensionality and compare the values at `i`.

Use `congrFun hx (Sum.inr i)` as an intermediate fact. Simplify using `using this`. Establish `hTR : T *ᵥ u ∈ LinearMap.range T.mulVecLin` using `⟨u, by simp⟩`. Establish `hBC : B *ᵥ w ∈ C` using `by rw [hBv]; exact Submodule.coe_mem _`. Establish `hTC : T *ᵥ u ∈ C`.

Establish `: T *ᵥ u = -(B *ᵥ w)` using `eq_neg_of_add_eq_zero_left h1`. Rewrite using `[this]`. Conclude with `C.neg_mem hBC`. Establish `hTu : T *ᵥ u = 0` using `Submodule.disjoint_def.1 hC.disjoint _ hTR hTC`. Establish `hBw : B *ᵥ w = 0` using `by rw [hTu, zero_add] at h1; exact h1`.

Establish `hw0 : w = 0`. Rewrite `hBw` using `[hBv]`. Establish `h3 : (∑ j, w j • b j : C) = 0` using `Subtype.ext hBw`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent w h3 j`.

Establish `hBu : Bᴴ *ᵥ u = 0` using `by rw [hw0, Matrix.mulVec_zero, add_zero] at h2; exact h2`. Establish `k1 : star u ᵥ* T = 0` using `star_vecMul_zero T u (by rw [hT]; exact hTu)`. Establish `k2 : star u ᵥ* B = 0` using `star_vecMul_zero B u hBu`. Establish `hsu : star u = 0`. Apply `_root_.dotProduct_eq_zero` to reduce the goal to its premises.

Introduce `y`. Establish `hy : y ∈ LinearMap.range T.mulVecLin ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨r, ⟨x', rfl⟩, c', hc', rfl⟩` from `Submodule.mem_sup.1 hy`. Establish `hc2 : c' = B *ᵥ (fun j => b.repr ⟨c', hc'⟩ j)`. Rewrite using `[hBv, b.sum_repr]`.

Rewrite using `[dotProduct_add, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, k1, hc2, Matrix.dotProduct_mulVec, k2]`. Simplify using the standard rewrite rules. Establish `hu0 : u = 0` using `by simpa using congrArg star hsu`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Conclude with `congrFun hu0 i`. Conclude with `congrFun hw0 i`. Introduce `x y hxy`. Use `hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem exists_B (a : ℕ) (T : Matrix (Fin a) (Fin a) K) (hT : Tᴴ = T) :
    ∃ B : Matrix (Fin a) (Fin (a - T.rank)) K,
      ∀ D : Matrix (Fin (a - T.rank)) (Fin (a - T.rank)) K,
        IsUnit (Matrix.fromBlocks T B Bᴴ D).det := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range T.mulVecLin)
  have hfin : Module.finrank K C = a - T.rank := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K (LinearMap.range T.mulVecLin) = T.rank := rfl
    omega
  let b := Module.finBasisOfFinrankEq K C hfin
  let B : Matrix (Fin a) (Fin (a - T.rank)) K := Matrix.of fun i j => (b j : Fin a → K) i
  have hBv : ∀ w : Fin (a - T.rank) → K, B *ᵥ w = ((∑ j, w j • b j : C) : Fin a → K) := by
    intro w
    ext i
    simp [B, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨B, fun D => ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ x, (Matrix.fromBlocks T B Bᴴ D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.fromBlocks_mulVec] at hx
    set u : Fin a → K := x ∘ Sum.inl with hu
    set w : Fin (a - T.rank) → K := x ∘ Sum.inr with hw
    have h1 : T *ᵥ u + B *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inl i)
      simpa using this
    have h2 : Bᴴ *ᵥ u + D *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inr i)
      simpa using this
    have hTR : T *ᵥ u ∈ LinearMap.range T.mulVecLin := ⟨u, by simp⟩
    have hBC : B *ᵥ w ∈ C := by rw [hBv]; exact Submodule.coe_mem _
    have hTC : T *ᵥ u ∈ C := by
      have : T *ᵥ u = -(B *ᵥ w) := eq_neg_of_add_eq_zero_left h1
      rw [this]; exact C.neg_mem hBC
    have hTu : T *ᵥ u = 0 := Submodule.disjoint_def.1 hC.disjoint _ hTR hTC
    have hBw : B *ᵥ w = 0 := by rw [hTu, zero_add] at h1; exact h1
    have hw0 : w = 0 := by
      rw [hBv] at hBw
      have h3 : (∑ j, w j • b j : C) = 0 := Subtype.ext hBw
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent w h3 j
    have hBu : Bᴴ *ᵥ u = 0 := by rw [hw0, Matrix.mulVec_zero, add_zero] at h2; exact h2
    have k1 : star u ᵥ* T = 0 := star_vecMul_zero T u (by rw [hT]; exact hTu)
    have k2 : star u ᵥ* B = 0 := star_vecMul_zero B u hBu
    have hsu : star u = 0 := by
      apply _root_.dotProduct_eq_zero
      intro y
      have hy : y ∈ LinearMap.range T.mulVecLin ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨r, ⟨x', rfl⟩, c', hc', rfl⟩ := Submodule.mem_sup.1 hy
      have hc2 : c' = B *ᵥ (fun j => b.repr ⟨c', hc'⟩ j) := by
        rw [hBv, b.sum_repr]
      rw [dotProduct_add, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, k1, hc2,
        Matrix.dotProduct_mulVec, k2]
      simp
    have hu0 : u = 0 := by simpa using congrArg star hsu
    funext i
    rcases i with i | i
    · exact congrFun hu0 i
    · exact congrFun hw0 i
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

omit [StarRing K] in
/- English proof (translation)
Establish `hsurj : Function.Surjective A.mulVec`. Establish `h1 : LinearMap.range A.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `hA`.

Introduce `y`. Establish `hy : y ∈ LinearMap.range A.mulVecLin` using `by rw [h1]; trivial`. Take `⟨x, hx⟩` from `hy`. Conclude with `⟨x, by simpa using hx⟩`. Take `⟨R, hR⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj`.

Set `φ : Matrix (Fin n) (Fin c) K →ₗ[K] Matrix (Fin a) (Fin c) K` to `{ toFun := fun Y => A * Y map_add' := fun x y => Matrix.mul_add A x y map_smul' := fun r x => by simp }`. Establish `hφa : ∀ Y, φ Y = A * Y` using `fun _ => rfl`. Establish `hφ : LinearMap.range φ = ⊤` using `LinearMap.range_eq_top.2 (fun Z => ⟨R * Z, by rw [hφa, ← Matrix.mul_assoc, hR, Matrix.one_mul]⟩)`. Establish `hdim` using `LinearMap.finrank_range_add_finrank_ker φ`. Rewrite `hdim` using `[hφ, finrank_top, Module.finrank_matrix, Module.finrank_matrix]`.

Simplify using `only [Fintype.card_fin, Module.finrank_self, mul_one] at hdim`. Establish `hker : Module.finrank K (LinearMap.ker φ) = (n - a) * c` using `by rw [Nat.sub_mul]; omega`. Set `e : {Y : Matrix (Fin n) (Fin c) K // A * Y = B} ≃ LinearMap.ker φ` to `{ toFun := fun Y => ⟨Y.1 - R * B, by`. Rewrite using `[LinearMap.mem_ker, hφa, Matrix.mul_sub, Y.2, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]⟩`. Use `invFun := fun Z => ⟨Z.1 + R * B, by`.

Establish `hz : A * Z.1 = 0` using `Z.2`. Rewrite using `[Matrix.mul_add, hz, ← Matrix.mul_assoc, hR, Matrix.one_mul, zero_add]⟩`. Use `left_inv := fun Y => by simp`. Use `right_inv := fun Z => by simp }`. Rewrite using `[Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hker]`.
-/
theorem card_fibre {n a c : ℕ} (A : Matrix (Fin a) (Fin n) K) (hA : A.rank = a)
    (B : Matrix (Fin a) (Fin c) K) :
    Nat.card {Y : Matrix (Fin n) (Fin c) K // A * Y = B} = Fintype.card K ^ ((n - a) * c) := by
  classical
  have hsurj : Function.Surjective A.mulVec := by
    have h1 : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hA
    intro y
    have hy : y ∈ LinearMap.range A.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by simpa using hx⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  let φ : Matrix (Fin n) (Fin c) K →ₗ[K] Matrix (Fin a) (Fin c) K :=
    { toFun := fun Y => A * Y
      map_add' := fun x y => Matrix.mul_add A x y
      map_smul' := fun r x => by simp }
  have hφa : ∀ Y, φ Y = A * Y := fun _ => rfl
  have hφ : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.2 (fun Z => ⟨R * Z, by rw [hφa, ← Matrix.mul_assoc, hR, Matrix.one_mul]⟩)
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφ, finrank_top, Module.finrank_matrix, Module.finrank_matrix] at hdim
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hdim
  have hker : Module.finrank K (LinearMap.ker φ) = (n - a) * c := by rw [Nat.sub_mul]; omega
  let e : {Y : Matrix (Fin n) (Fin c) K // A * Y = B} ≃ LinearMap.ker φ :=
    { toFun := fun Y => ⟨Y.1 - R * B, by
        rw [LinearMap.mem_ker, hφa, Matrix.mul_sub, Y.2, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]⟩
      invFun := fun Z => ⟨Z.1 + R * B, by
        have hz : A * Z.1 = 0 := Z.2
        rw [Matrix.mul_add, hz, ← Matrix.mul_assoc, hR, Matrix.one_mul, zero_add]⟩
      left_inv := fun Y => by simp
      right_inv := fun Z => by simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hker]

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
/- English proof (translation)
Rewrite using `[conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]`.
-/
theorem gram_reindex {ν ν' α α' : Type} [Fintype ν] [Fintype ν'] (e : ν' ≃ ν) (f : α' → α)
    (J : Matrix ν ν K) (Z : Matrix ν α K) :
    (Z.submatrix e f)ᴴ * J.submatrix e e * Z.submatrix e f = (Zᴴ * J * Z).submatrix f f := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

omit [Fintype K] in
/- English proof (translation)
Establish `: IsUnit ((gᴴ * J).det * g.det)` using `by rw [← det_mul, h]; exact hd`. Conclude with `isUnit_of_mul_isUnit_right this`.
-/
theorem unit_of_gram {ν : Type} [Fintype ν] [DecidableEq ν] (J g : Matrix ν ν K) (hd : IsUnit J.det)
    (h : gᴴ * J * g = J) : IsUnit g.det := by
  have : IsUnit ((gᴴ * J).det * g.det) := by rw [← det_mul, h]; exact hd
  exact isUnit_of_mul_isUnit_right this

/- English proof (translation)
Use `set e := Fintype.equivFin ι`. Establish `h` using `hUO (Fintype.card ι) (J.submatrix e.symm e.symm) (by rw [conjTranspose_submatrix, hJ]) (by rw [det_submatrix_equiv_self]; exact hd)`. Rewrite using `[← h]`. Use `congr 1`. Apply `Nat.card_congr` to reduce the goal to its premises.

Use `Equiv.subtypeEquiv (Matrix.reindex e e) (fun g => ?_)` and prove the remaining obligations. Rewrite using `[reindex_apply, gram_reindex]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Rewrite using `[hg]`.

Introduce `hg`. Use `congrArg (fun M => M.submatrix e e) hg` as an intermediate fact. Simplify using `using this`.
-/
theorem uo_gen {q : ℕ}
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι K) (hJ : Jᴴ = J) (hd : IsUnit J.det) :
    (Nat.card {g : Matrix ι ι K // gᴴ * J * g = J} : ℝ) =
      (q : ℝ) ^ ((Fintype.card ι) ^ 2) * densP (-1) q 1 (Fintype.card ι) := by
  set e := Fintype.equivFin ι
  have h := hUO (Fintype.card ι) (J.submatrix e.symm e.symm)
    (by rw [conjTranspose_submatrix, hJ]) (by rw [det_submatrix_equiv_self]; exact hd)
  rw [← h]
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Matrix.reindex e e) (fun g => ?_)
  rw [reindex_apply, gram_reindex]
  constructor
  · intro hg; rw [hg]
  · intro hg
    have := congrArg (fun M => M.submatrix e e) hg
    simpa using this

omit [Fintype K] in
/- English proof (translation)
Use `set e := Fintype.equivFin ν`. Use `set f := Fintype.equivFin α`. Take `⟨g, hg1, hg2⟩` from `hW _ _ (J.submatrix e.symm e.symm) (X.submatrix e.symm f.symm) (Y.submatrix e.symm f.symm) (by rw [conjTranspose_submatrix, hJ]) (by rw [det_submatrix_equiv_self]; exact hd) (by rw [rank_submatrix, hX]) (by rw [rank_submatrix, hY]) (by rw [gram_reindex, gram_reindex, h])`. Use `⟨g.submatrix e e, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `gram_reindex e e (J.submatrix e.symm e.symm) g`.

Rewrite `h1` using `[hg1]`. Simplify using `using h1`. Establish `h2` using `congrArg (fun M => M.submatrix e f) hg2`. Simplify using `only [← submatrix_mul_equiv g _ e e f] at h2`. Simplify using `using h2`.
-/
theorem witt_gen
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α] (J : Matrix ν ν K)
    (X Y : Matrix ν α K) (hJ : Jᴴ = J) (hd : IsUnit J.det) (hX : X.rank = Fintype.card α)
    (hY : Y.rank = Fintype.card α) (h : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix ν ν K, gᴴ * J * g = J ∧ g * X = Y := by
  set e := Fintype.equivFin ν
  set f := Fintype.equivFin α
  obtain ⟨g, hg1, hg2⟩ := hW _ _ (J.submatrix e.symm e.symm) (X.submatrix e.symm f.symm)
    (Y.submatrix e.symm f.symm) (by rw [conjTranspose_submatrix, hJ])
    (by rw [det_submatrix_equiv_self]; exact hd) (by rw [rank_submatrix, hX]) (by rw [rank_submatrix, hY])
    (by rw [gram_reindex, gram_reindex, h])
  refine ⟨g.submatrix e e, ?_, ?_⟩
  · have h1 := gram_reindex e e (J.submatrix e.symm e.symm) g
    rw [hg1] at h1
    simpa using h1
  · have h2 := congrArg (fun M => M.submatrix e f) hg2
    simp only [← submatrix_mul_equiv g _ e e f] at h2
    simpa using h2

omit [Fintype K] in
/- English proof (translation)
Take `⟨A, B, C, d, rfl⟩ : ∃ A B C d, k = fromBlocks A B C d` from `⟨_, _, _, _, (fromBlocks_toBlocks k).symm⟩`. Rewrite `h1` using `[fromBlocks_mul_fromRows]`. Take `⟨hA, hC⟩` from `fromRows_inj h1`. Simplify using `only [Matrix.mul_one, Matrix.mul_zero, add_zero] at hA hC`. Substitute `hA` using the available equality.

Substitute `hC` using the available equality. Rewrite `h2` using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Take `⟨-, hB, -, hd⟩` from `h2`. Simplify using `only [conjTranspose_one, Matrix.one_mul, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hB hd`. Establish `hB0 : B = 0`.

Use `congrArg (fun M => T⁻¹ * M) hB` as an intermediate fact. Simplify `this` using `[← Matrix.mul_assoc, nonsing_inv_mul T hdT]`. Substitute `hB0` using the available equality. Use `⟨d, rfl, ?_⟩` and prove the remaining obligations. Simplify using `using hd`.
-/
theorem stab_form {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hdT : IsUnit T.det)
    (k : Matrix (α ⊕ β) (α ⊕ β) K) (h1 : k * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) =
      (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K))
    (h2 : kᴴ * fromBlocks T 0 0 T' * k = fromBlocks T 0 0 T') :
    ∃ d : Matrix β β K, k = fromBlocks 1 0 0 d ∧ dᴴ * T' * d = T' := by
  obtain ⟨A, B, C, d, rfl⟩ : ∃ A B C d, k = fromBlocks A B C d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks k).symm⟩
  rw [fromBlocks_mul_fromRows] at h1
  obtain ⟨hA, hC⟩ := fromRows_inj h1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at hA hC
  subst hA; subst hC
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h2
  obtain ⟨-, hB, -, hd⟩ := h2
  simp only [conjTranspose_one, Matrix.one_mul, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hB hd
  have hB0 : B = 0 := by
    have := congrArg (fun M => T⁻¹ * M) hB
    simpa [← Matrix.mul_assoc, nonsing_inv_mul T hdT] using this
  subst hB0
  refine ⟨d, rfl, ?_⟩
  simpa using hd

omit [Fintype K] in
/- English proof (translation)
Apply `le_antisymm (rank_le_card_width X)` to reduce the goal to its premises. Establish `h1` using `rank_mul_le_right (Xᴴ * J) X`. Rewrite `h1` using `[h, rank_of_isUnit T ((isUnit_iff_isUnit_det T).2 hdT)]`. Conclude with `h1`.
-/
theorem rank_of_gram {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    (J : Matrix ν ν K) (T : Matrix α α K) (hdT : IsUnit T.det) (X : Matrix ν α K)
    (h : Xᴴ * J * X = T) : X.rank = Fintype.card α := by
  apply le_antisymm (rank_le_card_width X)
  have h1 := rank_mul_le_right (Xᴴ * J) X
  rw [h, rank_of_isUnit T ((isUnit_iff_isUnit_det T).2 hdT)] at h1
  exact h1

/- English proof (translation)
Use `set J := fromBlocks T 0 0 T' with hJdef`. Establish `hJ : Jᴴ = J` using `by rw [hJdef, fromBlocks_conjTranspose]; simp [hT, hT']`. Establish `hdJ : IsUnit J.det` using `by rw [hJdef, det_fromBlocks_zero₂₁]; exact hdT.mul hdT'`. Use `set X0 : Matrix (α ⊕ β) α K := fromRows 1 0 with hX0def`. Establish `hX0 : X0ᴴ * J * X0 = T`.

Rewrite using `[hX0def, conjTranspose_fromRows_eq_fromCols_conjTranspose, hJdef, fromCols_mul_fromBlocks, fromCols_mul_fromRows]`. Simplify using the standard rewrite rules. Establish `hch : ∀ X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T}, ∃ g, gᴴ * J * g = J ∧ g * X0 = X.1` using `fun X => witt_gen hW J X0 X.1 hJ hdJ (rank_of_gram J T hdT X0 hX0) (rank_of_gram J T hdT X.1 X.2) (by rw [hX0, X.2])`. Use `choose γ hγ1 hγ2 using hch`. Establish `hδ : ∀ d : Matrix β β K, fromBlocks (1 : Matrix α α K) 0 0 d * X0 = X0`.

Introduce `d`. Rewrite using `[hX0def, fromBlocks_mul_fromRows]`. Simplify using the standard rewrite rules. Establish `hδ2 : ∀ d : Matrix β β K, dᴴ * T' * d = T' → (fromBlocks (1 : Matrix α α K) 0 0 d)ᴴ * J * fromBlocks (1 : Matrix α α K) 0 0 d = J`. Introduce `d hd`.

Rewrite using `[hJdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[hd]`. Rewrite using `[← Nat.card_prod]`. Use `symm`. Use `Nat.card_eq_of_bijective (fun p : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} × {d : Matrix β β K // dᴴ * T' * d = T'} => (⟨γ p.1 * fromBlocks 1 0 0 p.2.1, ?_⟩ : {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * J * g = J})) ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨X, d⟩ ⟨X', d'⟩ h`. Establish `h' : γ X * fromBlocks 1 0 0 d.1 = γ X' * fromBlocks 1 0 0 d'.1` using `congrArg Subtype.val h`. Establish `hX : X = X'`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun M => M * X0) h'` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, hδ, hγ2] at this`. Conclude with `this`. Substitute `hX` using the available equality.

Establish `hu : IsUnit (γ X)` using `(isUnit_iff_isUnit_det _).2 (unit_of_gram J _ hdJ (hγ1 X))`. Establish `h3` using `hu.mul_left_cancel h'`. Rewrite `h3` using `[fromBlocks_inj]`. Establish `: d = d'` using `Subtype.ext h3.2.2.2`. Rewrite using `[this]`.

Introduce and unpack `⟨h, hh⟩`. Establish `hXg : (h * X0)ᴴ * J * (h * X0) = T`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `set X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} := ⟨h * X0, hXg⟩ with hXdef`.

Establish `hu : IsUnit (γ X).det` using `unit_of_gram J _ hdJ (hγ1 X)`. Use `set k := (γ X)⁻¹ * h with hk`. Establish `hγk : γ X * k = h` using `by rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]`. Establish `hk1 : k * X0 = X0`. Establish `e1 : γ X * X0 = h * X0` using `hγ2 X`.

Rewrite using `[hk, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]`. Establish `hk2 : kᴴ * J * k = J`. Establish `: (γ X * k)ᴴ * J * (γ X * k) = J` using `by rw [hγk]; exact hh`. Rewrite `this` using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨d, hd1, hd2⟩` from `stab_form T T' hdT k hk1 hk2`. Use `⟨(X, ⟨d, hd2⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show γ X * fromBlocks 1 0 0 d = h`. Rewrite using `[← hd1, hγk]`.
-/
theorem block_count
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hT : Tᴴ = T) (hdT : IsUnit T.det) (hT' : T'ᴴ = T')
    (hdT' : IsUnit T'.det) :
    Nat.card {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * fromBlocks T 0 0 T' * g = fromBlocks T 0 0 T'} =
      Nat.card {X : Matrix (α ⊕ β) α K // Xᴴ * fromBlocks T 0 0 T' * X = T} *
        Nat.card {d : Matrix β β K // dᴴ * T' * d = T'} := by
  classical
  set J := fromBlocks T 0 0 T' with hJdef
  have hJ : Jᴴ = J := by rw [hJdef, fromBlocks_conjTranspose]; simp [hT, hT']
  have hdJ : IsUnit J.det := by rw [hJdef, det_fromBlocks_zero₂₁]; exact hdT.mul hdT'
  set X0 : Matrix (α ⊕ β) α K := fromRows 1 0 with hX0def
  have hX0 : X0ᴴ * J * X0 = T := by
    rw [hX0def, conjTranspose_fromRows_eq_fromCols_conjTranspose, hJdef, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
    simp
  have hch : ∀ X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T}, ∃ g, gᴴ * J * g = J ∧ g * X0 = X.1 :=
    fun X => witt_gen hW J X0 X.1 hJ hdJ (rank_of_gram J T hdT X0 hX0) (rank_of_gram J T hdT X.1 X.2)
      (by rw [hX0, X.2])
  choose γ hγ1 hγ2 using hch
  have hδ : ∀ d : Matrix β β K, fromBlocks (1 : Matrix α α K) 0 0 d * X0 = X0 := by
    intro d
    rw [hX0def, fromBlocks_mul_fromRows]; simp
  have hδ2 : ∀ d : Matrix β β K, dᴴ * T' * d = T' →
      (fromBlocks (1 : Matrix α α K) 0 0 d)ᴴ * J * fromBlocks (1 : Matrix α α K) 0 0 d = J := by
    intro d hd
    rw [hJdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hd]
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective
    (fun p : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} × {d : Matrix β β K // dᴴ * T' * d = T'} =>
      (⟨γ p.1 * fromBlocks 1 0 0 p.2.1, ?_⟩ : {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * J * g = J})) ⟨?_, ?_⟩
  · rw [conjTranspose_mul]
    calc _ = (fromBlocks (1 : Matrix α α K) 0 0 p.2.1)ᴴ * ((γ p.1)ᴴ * J * γ p.1) *
          fromBlocks (1 : Matrix α α K) 0 0 p.2.1 := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hγ1, hδ2 _ p.2.2]
  · rintro ⟨X, d⟩ ⟨X', d'⟩ h
    have h' : γ X * fromBlocks 1 0 0 d.1 = γ X' * fromBlocks 1 0 0 d'.1 := congrArg Subtype.val h
    have hX : X = X' := by
      apply Subtype.ext
      have := congrArg (fun M => M * X0) h'
      simp only [Matrix.mul_assoc, hδ, hγ2] at this
      exact this
    subst hX
    have hu : IsUnit (γ X) := (isUnit_iff_isUnit_det _).2 (unit_of_gram J _ hdJ (hγ1 X))
    have h3 := hu.mul_left_cancel h'
    rw [fromBlocks_inj] at h3
    have : d = d' := Subtype.ext h3.2.2.2
    rw [this]
  · rintro ⟨h, hh⟩
    have hXg : (h * X0)ᴴ * J * (h * X0) = T := by
      rw [conjTranspose_mul]
      calc _ = X0ᴴ * (hᴴ * J * h) * X0 := by simp only [Matrix.mul_assoc]
        _ = T := by rw [hh, hX0]
    set X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} := ⟨h * X0, hXg⟩ with hXdef
    have hu : IsUnit (γ X).det := unit_of_gram J _ hdJ (hγ1 X)
    set k := (γ X)⁻¹ * h with hk
    have hγk : γ X * k = h := by rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    have hk1 : k * X0 = X0 := by
      have e1 : γ X * X0 = h * X0 := hγ2 X
      rw [hk, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    have hk2 : kᴴ * J * k = J := by
      have : (γ X * k)ᴴ * J * (γ X * k) = J := by rw [hγk]; exact hh
      rw [conjTranspose_mul] at this
      calc _ = kᴴ * ((γ X)ᴴ * J * γ X) * k := by rw [hγ1]
        _ = kᴴ * (γ X)ᴴ * J * (γ X * k) := by simp only [Matrix.mul_assoc]
        _ = J := this
    obtain ⟨d, hd1, hd2⟩ := stab_form T T' hdT k hk1 hk2
    refine ⟨(X, ⟨d, hd2⟩), ?_⟩
    apply Subtype.ext
    show γ X * fromBlocks 1 0 0 d = h
    rw [← hd1, hγk]

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Break down `lt_or_ge n (Fintype.card α) with hlt | hle` into its components or cases. Rewrite using `[densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]`. Establish `: IsEmpty {X : Matrix (Fin n) α K // Xᴴ * J * X = T}`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨X, hX⟩`. Establish `h1` using `rank_of_gram J T hdT X hX`. Establish `h2` using `rank_le_card_height X`. Rewrite `h2` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Use `set a := Fintype.card α with ha set D : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K := fromBlocks T 0 0 1 with hDdef`. Establish `hD : Dᴴ = D` using `by rw [hDdef, fromBlocks_conjTranspose]; simp [hT]`. Establish `hdD : IsUnit D.det` using `by rw [hDdef, det_fromBlocks_zero₂₁]; simpa using hdT`. Establish `hcard : Fintype.card (Fin n) = Fintype.card (α ⊕ Fin (n - a))`.

Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Take `⟨G, G', hGG', hG'G, hG⟩` from `exists_G htr hnorm hcard J D hJ hdJ hD hdD`. Establish `e1 : Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} = Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T}`. Apply `Nat.card_congr` to reduce the goal to its premises.

Use `⟨fun X => ⟨G' * X.1, ?_⟩, fun X => ⟨G * X.1, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hG, conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = T := by rw [hGG']; simpa using X.2`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `X`. Apply `Subtype.ext show G * (G' * X.1) = X.1` to reduce the goal to its premises.

Rewrite using `[← Matrix.mul_assoc, hGG', Matrix.one_mul]`. Introduce `X`. Apply `Subtype.ext show G' * (G * X.1) = X.1` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc, hG'G, Matrix.one_mul]`. Establish `e2` using `block_count hW T (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) hT hdT (by simp) (by simp)`.

Establish `u1` using `uo_gen hUO D hD hdD`. Establish `u2` using `uo_gen hUO (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) (by simp) (by simp)`. Rewrite `u1` using `[← hcard, Fintype.card_fin]`. Rewrite `u2` using `[Fintype.card_fin]`. Rewrite using `[e1]`.

Establish `e3 : (Nat.card {g : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K // gᴴ * D * g = D} : ℝ) = (Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) * (Nat.card {d : Matrix (Fin (n - a)) (Fin (n - a)) K // dᴴ * 1 * d = 1} : ℝ)`. Conclude with `e2` after adjusting the coercions. Rewrite `e3` using `[u1, u2]`. Establish `hsplit` using `densityProduct_split (-1) q 1 ((n - a : ℕ) : ℤ) n (by omega) (by omega)`. Establish `hpos : 0 < densP (-1) q 1 ((n - a : ℕ) : ℤ)` using `densityProduct_pos (-1) (Or.inr rfl) q hq _ _ le_rfl`.

Establish `hcast : ((n - a : ℕ) : ℤ) = (n : ℤ) - a` using `by omega`. Establish `hpw : (q : ℝ) ^ (n ^ 2) = (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * (q : ℝ) ^ ((n - a) ^ 2)`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne']`. Use `congr 1`. Move the coercions through the operations in `[hcast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `e3` using `[hsplit, hpw, hcast]`. Rewrite `hpos` using `[hcast]`. Establish `hpp : 0 < (q : ℝ) ^ ((n - a) ^ 2)` using `by positivity`. Establish `: ((Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) - (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - a + 1) n) * ((q : ℝ) ^ ((n - a) ^ 2) * densP (-1) q 1 ((n : ℤ) - a)) = 0`.

Take the linear combination `-e3`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h (by positivity)`.
-/
theorem nd_count {q : ℕ} (hq : 2 ≤ q)
    (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix α α K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) (hdT : IsUnit T.det) :
    (Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * (Fintype.card α) : ℤ) - (Fintype.card α) ^ 2) *
        densP (-1) q ((n : ℤ) - Fintype.card α + 1) n := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rcases lt_or_ge n (Fintype.card α) with hlt | hle
  · rw [densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]
    have : IsEmpty {X : Matrix (Fin n) α K // Xᴴ * J * X = T} := by
      constructor
      rintro ⟨X, hX⟩
      have h1 := rank_of_gram J T hdT X hX
      have h2 := rank_le_card_height X
      rw [Fintype.card_fin] at h2
      omega
    simp
  · set a := Fintype.card α with ha
    set D : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K := fromBlocks T 0 0 1 with hDdef
    have hD : Dᴴ = D := by rw [hDdef, fromBlocks_conjTranspose]; simp [hT]
    have hdD : IsUnit D.det := by rw [hDdef, det_fromBlocks_zero₂₁]; simpa using hdT
    have hcard : Fintype.card (Fin n) = Fintype.card (α ⊕ Fin (n - a)) := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega
    obtain ⟨G, G', hGG', hG'G, hG⟩ := exists_G htr hnorm hcard J D hJ hdJ hD hdD
    have e1 : Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} =
        Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} := by
      apply Nat.card_congr
      refine ⟨fun X => ⟨G' * X.1, ?_⟩, fun X => ⟨G * X.1, ?_⟩, ?_, ?_⟩
      · rw [← hG, conjTranspose_mul]
        calc _ = X.1ᴴ * (G * G')ᴴ * J * ((G * G') * X.1) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = T := by rw [hGG']; simpa using X.2
      · rw [conjTranspose_mul]
        calc _ = X.1ᴴ * (Gᴴ * J * G) * X.1 := by simp only [Matrix.mul_assoc]
          _ = T := by rw [hG]; exact X.2
      · intro X; apply Subtype.ext
        show G * (G' * X.1) = X.1
        rw [← Matrix.mul_assoc, hGG', Matrix.one_mul]
      · intro X; apply Subtype.ext
        show G' * (G * X.1) = X.1
        rw [← Matrix.mul_assoc, hG'G, Matrix.one_mul]
    have e2 := block_count hW T (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) hT hdT (by simp) (by simp)
    have u1 := uo_gen hUO D hD hdD
    have u2 := uo_gen hUO (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) (by simp) (by simp)
    rw [← hcard, Fintype.card_fin] at u1
    rw [Fintype.card_fin] at u2
    rw [e1]
    have e3 : (Nat.card {g : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K // gᴴ * D * g = D} : ℝ) =
        (Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) *
        (Nat.card {d : Matrix (Fin (n - a)) (Fin (n - a)) K // dᴴ * 1 * d = 1} : ℝ) := by
      exact_mod_cast e2
    rw [u1, u2] at e3
    have hsplit := densityProduct_split (-1) q 1 ((n - a : ℕ) : ℤ) n (by omega) (by omega)
    have hpos : 0 < densP (-1) q 1 ((n - a : ℕ) : ℤ) := densityProduct_pos (-1) (Or.inr rfl) q hq _ _ le_rfl
    have hcast : ((n - a : ℕ) : ℤ) = (n : ℤ) - a := by omega
    have hpw : (q : ℝ) ^ (n ^ 2) = (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * (q : ℝ) ^ ((n - a) ^ 2) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne']
      congr 1
      push_cast [hcast]
      ring
    rw [hsplit, hpw, hcast] at e3
    rw [hcast] at hpos
    have hpp : 0 < (q : ℝ) ^ ((n - a) ^ 2) := by positivity
    have : ((Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) -
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - a + 1) n) *
        ((q : ℝ) ^ ((n - a) ^ 2) * densP (-1) q 1 ((n : ℤ) - a)) = 0 := by
      linear_combination -e3
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (by positivity)

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Formalism.FourierDecayAlt.S3

/- English proof (translation)
Use `Fintype.ofFinite A` as an intermediate fact. Rewrite using `[← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl (fun a _ => h a), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.
-/
theorem card_of_fibres {P A : Type} [Finite P] [Finite A] (f : P → A) (m : ℝ)
    (h : ∀ a, (Nat.card {p // f p = a} : ℝ) = m) : (Nat.card P : ℝ) = Nat.card A * m := by
  classical
  have := Fintype.ofFinite A
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
/- English proof (translation)
Establish `hsurj : Function.Surjective Xᵀ.mulVec`. Establish `h1 : LinearMap.range Xᵀ.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Use `rank_transpose X` as an intermediate fact.

Rewrite `this` using `[hX]`. Conclude with `this`. Introduce `y`. Establish `hy : y ∈ LinearMap.range Xᵀ.mulVecLin` using `by rw [h1]; trivial`. Take `⟨x, hx⟩` from `hy`.

Conclude with `⟨x, by rw [← hx, Matrix.mulVecLin_apply]⟩`. Take `⟨R, hR⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj`. Establish `h2 : Rᵀ * X = 1`. Use `congrArg transpose hR` as an intermediate fact. Simplify `this` using `[transpose_mul]`.

Establish `h3 : Xᴴ * Rᵀᴴ = 1`. Use `congrArg conjTranspose h2` as an intermediate fact. Simplify `this` using `[conjTranspose_mul]`. Establish `h4 : (Xᴴ * J) * (J⁻¹ * Rᵀᴴ) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc J, mul_nonsing_inv _ hdJ, Matrix.one_mul, h3]`.

Apply `le_antisymm` to reduce the goal to its premises. Simplify using `using rank_le_card_height (Xᴴ * J)`. Use `rank_mul_le_left (Xᴴ * J) (J⁻¹ * Rᵀᴴ)` as an intermediate fact. Rewrite `this` using `[h4, rank_one, Fintype.card_fin]`. Conclude with `this`.
-/
theorem rank_conj_mul {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a)
    (J : Matrix (Fin n) (Fin n) K) (hdJ : IsUnit J.det) : (Xᴴ * J).rank = a := by
  have hsurj : Function.Surjective Xᵀ.mulVec := by
    have h1 : LinearMap.range Xᵀ.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      have := rank_transpose X
      rw [hX] at this
      exact this
    intro y
    have hy : y ∈ LinearMap.range Xᵀ.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by rw [← hx, Matrix.mulVecLin_apply]⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  have h2 : Rᵀ * X = 1 := by
    have := congrArg transpose hR
    simpa [transpose_mul] using this
  have h3 : Xᴴ * Rᵀᴴ = 1 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul] using this
  have h4 : (Xᴴ * J) * (J⁻¹ * Rᵀᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, mul_nonsing_inv _ hdJ, Matrix.one_mul, h3]
  apply le_antisymm
  · simpa using rank_le_card_height (Xᴴ * J)
  · have := rank_mul_le_left (Xᴴ * J) (J⁻¹ * Rᵀᴴ)
    rw [h4, rank_one, Fintype.card_fin] at this
    exact this

omit [Fintype K] in
/- English proof (translation)
Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]`.
-/
theorem gram_fromCols {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K) :
    (fromCols X Y)ᴴ * J * fromCols X Y =
      fromBlocks (Xᴴ * J * X) (Xᴴ * J * Y) (Yᴴ * J * X) (Yᴴ * J * Y) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]

omit [Fintype K] in
/- English proof (translation)
Establish `hL : (S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y = 1`. Rewrite using `[Matrix.mul_assoc, h, nonsing_inv_mul _ hS]`. Establish `hX : X = fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)`. Rewrite using `[fromCols_mul_fromRows]`. Simplify using the standard rewrite rules.

Establish `hM : ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) * (S⁻¹ * ((fromCols X Y)ᴴ * J))) * X = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hX]`. Use `_ = (fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) * (((S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y) * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by`. Rewrite using `[hL, Matrix.one_mul, fromCols_mul_fromRows]`. Simplify using the standard rewrite rules. Apply `le_antisymm (rank_le_card_width X)` to reduce the goal to its premises. Use `rank_mul_le_right ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) * (S⁻¹ * ((fromCols X Y)ᴴ * J))) X` as an intermediate fact.

Rewrite `this` using `[hM, rank_one]`. Conclude with `this`.
-/
theorem rank_left_block {ν α β : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K)
    (S : Matrix (α ⊕ β) (α ⊕ β) K) (hS : IsUnit S.det)
    (h : (fromCols X Y)ᴴ * J * fromCols X Y = S) : X.rank = Fintype.card α := by
  have hL : (S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y = 1 := by
    rw [Matrix.mul_assoc, h, nonsing_inv_mul _ hS]
  have hX : X = fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) := by
    rw [fromCols_mul_fromRows]; simp
  have hM : ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) * X = 1 := by
    calc _ = ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (S⁻¹ * ((fromCols X Y)ᴴ * J))) *
          (fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          rw [← hX]
      _ = (fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (((S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y) *
            (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hL, Matrix.one_mul, fromCols_mul_fromRows]
          simp
  apply le_antisymm (rank_le_card_width X)
  have := rank_mul_le_right ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) X
  rw [hM, rank_one] at this
  exact this

/- English proof (translation)
Establish `hq : 2 ≤ q` using `two_le_q hc`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `hrk : T.rank ≤ a` using `by simpa using rank_le_card_width T`. Break down `lt_or_ge n a with hlt | hle` into its components or cases. Rewrite using `[densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]`.

Establish `: IsEmpty {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T}`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, hX, -⟩`. Establish `h2` using `rank_le_card_height X`. Rewrite `h2` using `[Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Take `⟨c, hcdef⟩ : ∃ c, c = a - T.rank` from `⟨_, rfl⟩`. Establish `hex` using `exists_B a T hT`. Rewrite `hex` using `[← hcdef]`.

Take `⟨B, hB⟩` from `hex`. Set `P` to `{p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin c) K // p.1.rank = a ∧ p.1ᴴ * J * p.1 = T ∧ p.1ᴴ * J * p.2 = B}`. Set `f1 : P → {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T}` to `fun p => ⟨p.1.1, p.2.1, p.2.2.1⟩`. Establish `c1 : (Nat.card P : ℝ) = Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} * (((Fintype.card K) ^ ((n - a) * c) : ℕ) : ℝ)`. Apply `card_of_fibres f1` to reduce the goal to its premises.

Introduce `X`. Use `congr 1`. Rewrite using `[← card_fibre (X.1ᴴ * J) (rank_conj_mul X.1 X.2.1 J hdJ) B]`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `⟨fun p => ⟨p.1.1.2, ?_⟩, fun Y => ⟨⟨(X.1, Y.1), X.2.1, X.2.2, Y.2⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `h : p.1.1.1 = X.1` using `congrArg Subtype.val p.2`. Rewrite using `[← h]`. Conclude with `p.1.2.2.2`. Introduce `p`. Establish `h : p.1.1.1 = X.1` using `congrArg Subtype.val p.2`.

Conclude with `Subtype.ext (Subtype.ext (Prod.ext h.symm rfl))`. Introduce `Y`. Both sides reduce to the same expression. Establish `hherm : ∀ Y : Matrix (Fin n) (Fin c) K, (Yᴴ * J * Y)ᴴ = Yᴴ * J * Y`. Introduce `Y`.

Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`. Set `f2 : P → {D : Matrix (Fin c) (Fin c) K // Dᴴ = D}` to `fun p => ⟨p.1.2ᴴ * J * p.1.2, hherm _⟩`. Establish `c2 : (Nat.card P : ℝ) = Nat.card {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} * ((q : ℝ) ^ ((2 * n * (Fintype.card (Fin a ⊕ Fin c)) : ℤ) - (Fintype.card (Fin a ⊕ Fin c)) ^ 2) * densP (-1) q ((n : ℤ) - Fintype.card (Fin a ⊕ Fin c) + 1) n)`. Apply `card_of_fibres f2` to reduce the goal to its premises. Introduce `D`.

Establish `hS : (fromBlocks T B Bᴴ D.1)ᴴ = fromBlocks T B Bᴴ D.1`. Rewrite using `[fromBlocks_conjTranspose, hT, D.2, conjTranspose_conjTranspose]`. Rewrite using `[← nd_count hq (exists_trace_ne hs hc) (norm_surj hs hc) hUO hW n J (fromBlocks T B Bᴴ D.1) hJ hdJ hS (hB D.1)]`. Use `congr 1`. Apply `Nat.card_congr` to reduce the goal to its premises.

Use `⟨fun p => ⟨fromCols p.1.1.1 p.1.1.2, ?_⟩, fun Z => ⟨⟨(Z.1.toCols₁, Z.1.toCols₂), ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h : p.1.1.2ᴴ * J * p.1.1.2 = D.1` using `congrArg Subtype.val p.2`. Rewrite using `[gram_fromCols, p.1.2.2.1, p.1.2.2.2, h]`. Use `congr 1`. Establish `h5` using `congrArg conjTranspose p.1.2.2.2`.

Rewrite `h5` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, ← Matrix.mul_assoc]`. Conclude with `h5`. Establish `h` using `Z.2`. Rewrite `h` using `[← fromCols_toCols Z.1]`. Simplify using `using rank_left_block J _ _ _ (hB D.1) h`.

Establish `h` using `Z.2`. Rewrite `h` using `[← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj]`. Conclude with `h.1`. Establish `h` using `Z.2`. Rewrite `h` using `[← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj]`.

Conclude with `h.2.1`. Establish `h` using `Z.2`. Rewrite `h` using `[← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj]`. Conclude with `Subtype.ext h.2.2.2`. Introduce `p`.

Conclude with `Subtype.ext (Subtype.ext (Prod.ext (toCols₁_fromCols _ _) (toCols₂_fromCols _ _)))`. Introduce `Z`. Conclude with `Subtype.ext (fromCols_toCols _)`. Rewrite `c2` using `[card_herm hs hc c, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Rewrite `c2` using `[c1, hc]`.

Establish `hcc : (c : ℤ) = (a : ℤ) - T.rank` using `by omega`. Establish `hlo : (n : ℤ) - a - ((a : ℤ) - T.rank) + 1 = (n : ℤ) - ((a + c : ℕ) : ℤ) + 1` using `by push_cast; omega`. Rewrite using `[hlo]`. Establish `hna : ((n - a : ℕ) : ℤ) = (n : ℤ) - a` using `by omega`. Establish `hpw : (((q ^ (c ^ 2) : ℕ) : ℝ)) * (q : ℝ) ^ ((2 * n * ((a + c : ℕ) : ℤ) : ℤ) - ((a + c : ℕ) : ℤ) ^ 2) = (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * ((((q ^ 2) ^ ((n - a) * c) : ℕ)) : ℝ)`.

Use `push_cast`. Rewrite using `[← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne', ← zpow_add₀ hq0.ne']`. Use `congr 1`. Move the coercions through the operations in `[hna]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpp : (0 : ℝ) < (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ)`. Conclude with `Nat.pos_of_ne_zero (by positivity)` after adjusting the coercions. Establish `: ((Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) - (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n) * (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ) = 0`. Take the linear combination `c2 + densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n * hpw`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h hpp.ne'`.
-/
theorem herm_count_star {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin a) (Fin a) K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) :
    (Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) *
        densP (-1) q ((n : ℤ) - a - ((a : ℤ) - T.rank) + 1) n := by
  classical
  have hq : 2 ≤ q := two_le_q hc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hrk : T.rank ≤ a := by simpa using rank_le_card_width T
  rcases lt_or_ge n a with hlt | hle
  · rw [densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]
    have : IsEmpty {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} := by
      constructor
      rintro ⟨X, hX, -⟩
      have h2 := rank_le_card_height X
      rw [Fintype.card_fin] at h2
      omega
    simp
  · obtain ⟨c, hcdef⟩ : ∃ c, c = a - T.rank := ⟨_, rfl⟩
    have hex := exists_B a T hT
    rw [← hcdef] at hex
    obtain ⟨B, hB⟩ := hex
    let P := {p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin c) K //
      p.1.rank = a ∧ p.1ᴴ * J * p.1 = T ∧ p.1ᴴ * J * p.2 = B}

    let f1 : P → {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} :=
      fun p => ⟨p.1.1, p.2.1, p.2.2.1⟩
    have c1 : (Nat.card P : ℝ) =
        Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} *
          (((Fintype.card K) ^ ((n - a) * c) : ℕ) : ℝ) := by
      apply card_of_fibres f1
      intro X
      congr 1
      rw [← card_fibre (X.1ᴴ * J) (rank_conj_mul X.1 X.2.1 J hdJ) B]
      apply Nat.card_congr
      refine ⟨fun p => ⟨p.1.1.2, ?_⟩, fun Y => ⟨⟨(X.1, Y.1), X.2.1, X.2.2, Y.2⟩, rfl⟩, ?_, ?_⟩
      · have h : p.1.1.1 = X.1 := congrArg Subtype.val p.2
        rw [← h]; exact p.1.2.2.2
      · intro p
        have h : p.1.1.1 = X.1 := congrArg Subtype.val p.2
        exact Subtype.ext (Subtype.ext (Prod.ext h.symm rfl))
      · intro Y; rfl

    have hherm : ∀ Y : Matrix (Fin n) (Fin c) K, (Yᴴ * J * Y)ᴴ = Yᴴ * J * Y := by
      intro Y
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
    let f2 : P → {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} := fun p => ⟨p.1.2ᴴ * J * p.1.2, hherm _⟩
    have c2 : (Nat.card P : ℝ) = Nat.card {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} *
        ((q : ℝ) ^ ((2 * n * (Fintype.card (Fin a ⊕ Fin c)) : ℤ) - (Fintype.card (Fin a ⊕ Fin c)) ^ 2) *
          densP (-1) q ((n : ℤ) - Fintype.card (Fin a ⊕ Fin c) + 1) n) := by
      apply card_of_fibres f2
      intro D
      have hS : (fromBlocks T B Bᴴ D.1)ᴴ = fromBlocks T B Bᴴ D.1 := by
        rw [fromBlocks_conjTranspose, hT, D.2, conjTranspose_conjTranspose]
      rw [← nd_count hq (exists_trace_ne hs hc) (norm_surj hs hc) hUO hW n J (fromBlocks T B Bᴴ D.1)
        hJ hdJ hS (hB D.1)]
      congr 1
      apply Nat.card_congr
      refine ⟨fun p => ⟨fromCols p.1.1.1 p.1.1.2, ?_⟩,
        fun Z => ⟨⟨(Z.1.toCols₁, Z.1.toCols₂), ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · have h : p.1.1.2ᴴ * J * p.1.1.2 = D.1 := congrArg Subtype.val p.2
        rw [gram_fromCols, p.1.2.2.1, p.1.2.2.2, h]
        congr 1
        have h5 := congrArg conjTranspose p.1.2.2.2
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
          ← Matrix.mul_assoc] at h5
        exact h5
      · have h := Z.2
        rw [← fromCols_toCols Z.1] at h
        simpa using rank_left_block J _ _ _ (hB D.1) h
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact h.1
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact h.2.1
      · have h := Z.2
        rw [← fromCols_toCols Z.1, gram_fromCols, fromBlocks_inj] at h
        exact Subtype.ext h.2.2.2
      · intro p
        exact Subtype.ext (Subtype.ext (Prod.ext (toCols₁_fromCols _ _) (toCols₂_fromCols _ _)))
      · intro Z
        exact Subtype.ext (fromCols_toCols _)
    rw [card_herm hs hc c, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at c2
    rw [c1, hc] at c2
    have hcc : (c : ℤ) = (a : ℤ) - T.rank := by omega
    have hlo : (n : ℤ) - a - ((a : ℤ) - T.rank) + 1 = (n : ℤ) - ((a + c : ℕ) : ℤ) + 1 := by
      push_cast; omega
    rw [hlo]
    have hna : ((n - a : ℕ) : ℤ) = (n : ℤ) - a := by omega
    have hpw : (((q ^ (c ^ 2) : ℕ) : ℝ)) * (q : ℝ) ^ ((2 * n * ((a + c : ℕ) : ℤ) : ℤ) - ((a + c : ℕ) : ℤ) ^ 2) =
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * ((((q ^ 2) ^ ((n - a) * c) : ℕ)) : ℝ) := by
      push_cast
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne', ← zpow_add₀ hq0.ne']
      congr 1
      push_cast [hna]
      ring
    have hpp : (0 : ℝ) < (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by positivity)
    have : ((Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ Xᴴ * J * X = T} : ℝ) -
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n) *
        (((q ^ 2) ^ ((n - a) * c) : ℕ) : ℝ) = 0 := by
      linear_combination c2 + densP (-1) q ((n : ℤ) - ((a + c : ℕ) : ℤ) + 1) n * hpw
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hpp.ne'

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5

/- English proof (translation)
Introduce `hUO hW K _ _ q n a J T hc hJ hdJ hT`. Set `_ : StarRing K` to `starRingOfCard K q hc`. Establish `hs : ∀ x : K, star x = x ^ q` using `fun x => rfl`. Establish `hUO' : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det → (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) = (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b`. Introduce `b J h1 h2`.

Use `hUO K q b J hc (by rw [fconj_eq hs]; exact h1) h2` as an intermediate fact. Simplify `this` using `only [fconj_eq hs]`. Establish `hW' : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K), Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y → ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y`. Introduce `n a J X Y h1 h2 h3 h4 h5`. Use `hW K q n a J X Y hc (by rw [fconj_eq hs]; exact h1) h2 h3 h4 (by simp only [fconj_eq hs]; exact h5)` as an intermediate fact.

Simplify `this` using `only [fconj_eq hs]`. Use `herm_count_star hs hc hUO' hW' n a J T (by rw [← fconj_eq hs]; exact hJ) hdJ (by rw [← fconj_eq hs]; exact hT)` as an intermediate fact. Simplify `this` using `only [fconj_eq hs]`.
-/
theorem hermFrameCount_statement : Formalism.FourierDecayAlt.S3.HermFrameCount := by
  intro hUO hW K _ _ q n a J T hc hJ hdJ hT
  let _ : StarRing K := starRingOfCard K q hc
  have hs : ∀ x : K, star x = x ^ q := fun x => rfl
  have hUO' : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b := by
    intro b J h1 h2
    have := hUO K q b J hc (by rw [fconj_eq hs]; exact h1) h2
    simpa only [fconj_eq hs] using this
  have hW' : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y := by
    intro n a J X Y h1 h2 h3 h4 h5
    have := hW K q n a J X Y hc (by rw [fconj_eq hs]; exact h1) h2 h3 h4
      (by simp only [fconj_eq hs]; exact h5)
    simpa only [fconj_eq hs] using this
  have := herm_count_star hs hc hUO' hW' n a J T (by rw [← fconj_eq hs]; exact hJ) hdJ
    (by rw [← fconj_eq hs]; exact hT)
  simpa only [fconj_eq hs] using this

end Formalism.FourierDecayAlt.P
