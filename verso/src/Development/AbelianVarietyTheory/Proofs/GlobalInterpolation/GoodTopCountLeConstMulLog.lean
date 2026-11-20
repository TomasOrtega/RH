import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

/- English proof (translation)
Use `set L := Real.log x with hLdef`. Establish `hu : (G.goodU de : ℝ) * de ≤ 2`. Unfold `G.goodU`. Establish `h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de` using `mul_le_mul_of_nonneg_right h1.le hde.le`.

Establish `h3 : (1 / de + 1) * de = 1 + de` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : (0 : ℝ) < 10 ^ (6 * r + 1)` using `by positivity`. Establish `hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L`. Unfold `G.orbitSmallMultiplicity`.

Establish `he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) = (h + 3) * 10 ^ (6 * r + 1) * L`. Rewrite using `[zpow_neg, zpow_natCast, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Establish `h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1` using `Nat.ceil_lt_add_one (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hG : (G.goodG' r de h x : ℝ) * de ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L`. Unfold `G.goodG' G.goodEll`. Establish `he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de = ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de))` using `by push_cast; ring`. Rewrite using `[he]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)` to reduce the goal to its premises. Check the signs of the components of the expression. Use `_ = _ := by ring`. Establish `hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L`.

Establish `h2 : (1 / 2 : ℝ) < Real.log 2` using `by have := Real.log_two_gt_d9; linarith`. Establish `: Real.logb 2 x ≤ 2 * L`. Unfold `Real.logb`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left this (by linarith)`. Unfold `G.orbitWindowCount`. Use `set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Establish `hE : 0 < 6 * Real.exp 1` using `by positivity`. Establish `h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L`. Rewrite using `[mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]`. Conclude with `mul_le_mul_of_nonneg_left hG hE.le`. Establish `h1' : 0 ≤ 6 * Real.exp 1 * A * L` using `by positivity`.

Establish `h2' : 0 ≤ (h + 3) * 2 * L` using `by positivity`. Establish `hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤ 6 * Real.exp 1 * A * L + (h + 3) * 2 * L` using `max_le (by linarith) (by linarith)`. Establish `hc` using `Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))`. Rewrite using `[Nat.cast_add, Nat.cast_one]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem goodTopCount_le_const_mul_log (r : ℕ) (de h x : ℝ) (hde : 0 < de) (hde1 : de ≤ 1)
    (hh : 0 ≤ h) (hL : 1 ≤ Real.log x) :
    (G.orbitWindowCount r de h x : ℝ) ≤
      (6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2) * Real.log x := by
  set L := Real.log x with hLdef
  have hu : (G.goodU de : ℝ) * de ≤ 2 := by
    unfold G.goodU
    have h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de := mul_le_mul_of_nonneg_right h1.le hde.le
    have h3 : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hT : (0 : ℝ) < 10 ^ (6 * r + 1) := by positivity
  have hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L := by
    unfold G.orbitSmallMultiplicity
    have he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        (h + 3) * 10 ^ (6 * r + 1) * L := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]; ring
    rw [he]
    have h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hG : (G.goodG' r de h x : ℝ) * de ≤
      (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L := by
    unfold G.goodG' G.goodEll
    have he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de =
        ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de)) := by
      push_cast; ring
    rw [he]
    calc _ ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * L) * (((6 * r + 1 : ℕ) : ℝ) * 2) := by
          apply mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
          positivity
      _ = _ := by ring
  have hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.logb 2 x ≤ 2 * L := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  unfold G.orbitWindowCount
  set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE : 0 < 6 * Real.exp 1 := by positivity
  have h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L := by
    rw [mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hG hE.le
  have h1' : 0 ≤ 6 * Real.exp 1 * A * L := by positivity
  have h2' : 0 ≤ (h + 3) * 2 * L := by positivity
  have hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤
      6 * Real.exp 1 * A * L + (h + 3) * 2 * L := max_le (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de)
    ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

/- English proof (translation)
Introduce `eps he _`. Take `⟨x1, hx1⟩` from `Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)`. Use `set h : ℝ := 2 + 8 * eps with hh`. Use `set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr`. Use `⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) + (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩` and prove the remaining obligations.

Introduce `s hs hx`. Establish `hx0 : 0 < s.x` using `lt_trans one_pos s.one_lt_alt`. Establish `hL : 1 ≤ Real.log s.x`. Rewrite using `[Real.le_log_iff_exp_le hx0]`. Conclude with `le_trans (le_max_right _ _) hx`.

Establish `hP : 0 < s.x ^ s.eps` using `Real.rpow_pos_of_pos hx0 _`. Establish `hlog : Real.log s.x ≤ s.x ^ s.eps`. Use `hx1 s.x (le_trans (le_max_left _ _) hx)` as an intermediate fact. Rewrite `this` using `[one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le]`. Conclude with `this`.

Establish `hhG : G.hG s = h` using `by unfold G.hG; rw [hs]`. Establish `hrG : G.rG s = r` using `by unfold G.rG G.KG; rw [hhG, hs]`. Establish `hN1 : 1 ≤ G.N1 s` using `by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _`. Establish `hN` using `goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _) (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith)) (by positivity) hL`. Establish `hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x` using `by unfold G.N1; rw [hhG, hrG]`.

Rewrite `hN` using `[← hNe]`. Generalize the expression as in `6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) + (h + 3) * 2 + 2 = CN at hN ⊢`. Use `⟨hN1, hN, fun K hK => ?_⟩` and prove the remaining obligations. Establish `ha : Real.log s.a = Real.log s.x + s.x ^ s.eps`. Unfold `Scale.a Scale.b Scale.L`.

Rewrite using `[Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]`. Establish `hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ)` using `by exact_mod_cast hN1`. Establish `hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2` using `one_le_pow₀ hN1'`. Establish `hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2` using `pow_le_pow_left₀ (by linarith) hN 2`. Unfold `G.La`.

Rewrite using `[ha]`. Prove the components needed by the constructor for the conclusion. Establish `h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2` using `one_le_mul_of_one_le_of_one_le hK hsq`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)` to reduce the goal to its premises. Establish `: 0 ≤ K.La` using `by linarith`. Check the signs of the components of the expression. Use `_ = _ := by ring`.
-/
theorem topCount_and_lambda_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CN x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → 1 ≤ G.N1 s ∧ (G.N1 s : ℝ) ≤ CN * Real.log s.x ∧
      ∀ K : G.Consts, 1 ≤ K.La → s.x ^ s.eps ≤ G.La K s ∧
        G.La K s ≤ K.La * CN ^ 2 * Real.log s.x ^ 2 * (2 * s.x ^ s.eps) := by
  intro eps he _
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)
  set h : ℝ := 2 + 8 * eps with hh
  set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr
  refine ⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩
  intro s hs hx
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hL : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have hP : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log s.x ≤ s.x ^ s.eps := by
    have := hx1 s.x (le_trans (le_max_left _ _) hx)
    rw [one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le] at this
    exact this
  have hhG : G.hG s = h := by unfold G.hG; rw [hs]
  have hrG : G.rG s = r := by unfold G.rG G.KG; rw [hhG, hs]
  have hN1 : 1 ≤ G.N1 s := by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _
  have hN := goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith))
    (by positivity) hL
  have hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x := by unfold G.N1; rw [hhG, hrG]
  rw [← hNe] at hN
  generalize 6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2 = CN at hN ⊢
  refine ⟨hN1, hN, fun K hK => ?_⟩
  have ha : Real.log s.a = Real.log s.x + s.x ^ s.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ) := by exact_mod_cast hN1
  have hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2 := one_le_pow₀ hN1'
  have hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2 := pow_le_pow_left₀ (by linarith) hN 2
  unfold G.La
  rw [ha]
  constructor
  · have h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hK hsq
    nlinarith
  · calc K.La * (G.N1 s : ℝ) ^ 2 * (Real.log s.x + s.x ^ s.eps)
        ≤ K.La * (CN * Real.log s.x) ^ 2 * (2 * s.x ^ s.eps) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)
          have : 0 ≤ K.La := by linarith
          positivity
      _ = _ := by ring

end GlobalTheory
