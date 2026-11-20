import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, e = k + 1` from `⟨e - 1, by omega⟩`. Use `haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩`. Establish `hn : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k` using `by ring`. Establish `hpos : 0 < 2 ^ k` using `by positivity`. Establish `hlt : 2 ^ k < 2 ^ (k + 1)` using `by omega`.

Establish `hne : (0 : ZMod (2 ^ (k + 1))) ≠ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))`. Introduce `h`. Establish `h2` using `congrArg ZMod.val h`. Rewrite `h2` using `[ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]`. Use linear arithmetic over natural numbers and integers.

Establish `hset : Finset.univ.filter (fun c : ZMod (2 ^ (k + 1)) => c + c = 0) = {0, ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))}`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`.

Establish `hv` using `congrArg ZMod.val hc`. Rewrite `hv` using `[ZMod.val_add, ZMod.val_zero]`. Establish `hcl` using `ZMod.val_lt c`. Rewrite using `[← ZMod.natCast_zmod_val c]`. Break down `Nat.lt_or_ge (c.val + c.val) (2 ^ (k + 1)) with h1 | h1` into its components or cases.

Rewrite `hv`, `left` using `[Nat.mod_eq_of_lt h1]`. Establish `: c.val = 0` using `by omega`. Rewrite using `[this, Nat.cast_zero]`. Rewrite `hv`, `right` using `[Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]`. Establish `: c.val = 2 ^ k` using `by omega`.

Rewrite using `[this]`. Introduce and unpack `(rfl | rfl)`. Simplify using the standard rewrite rules. Rewrite using `[← Nat.cast_add, ← hn, ZMod.natCast_self]`. Rewrite using `[hset, Finset.card_pair hne]`.
-/
private lemma gl2b2_twoTors (e : ℕ) (he : 1 ≤ e) :
    (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0)).card = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hn : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  have hpos : 0 < 2 ^ k := by positivity
  have hlt : 2 ^ k < 2 ^ (k + 1) := by omega
  have hne : (0 : ZMod (2 ^ (k + 1))) ≠ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
    intro h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at h2
    omega
  have hset : Finset.univ.filter (fun c : ZMod (2 ^ (k + 1)) => c + c = 0) =
      {0, ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hv := congrArg ZMod.val hc
      rw [ZMod.val_add, ZMod.val_zero] at hv
      have hcl := ZMod.val_lt c
      rw [← ZMod.natCast_zmod_val c]
      rcases Nat.lt_or_ge (c.val + c.val) (2 ^ (k + 1)) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1] at hv
        left
        have : c.val = 0 := by omega
        rw [this, Nat.cast_zero]
      · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hv
        right
        have : c.val = 2 ^ k := by omega
        rw [this]
    · rintro (rfl | rfl)
      · simp
      · rw [← Nat.cast_add, ← hn, ZMod.natCast_self]
  rw [hset, Finset.card_pair hne]

/- English proof (translation)
Introduce `e he`. Establish `: (Finset.univ.filter (fun g : ZMod 2 × ZMod 2 × ZMod (2 ^ e) => g + g = 0)) = (Finset.univ : Finset (ZMod 2)) ×ˢ ((Finset.univ : Finset (ZMod 2)) ×ˢ (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0)))`. Use extensionality with `⟨a, b, c⟩`. Simplify using `only [mem_filter, mem_univ, true_and, mem_product, Prod.mk_add_mk, Prod.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, _, h⟩`. Conclude with `h`. Introduce `h`. Conclude with `⟨CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b, h⟩`. Rewrite using `[this, Finset.card_product, Finset.card_product, gl2b2_twoTors e he]`.

Simplify using the standard rewrite rules.
-/
theorem real_character_count : Formalism.HermitianLattices.ZeroFreeRegionGL2.RealCharCount := by
  intro e he
  have : (Finset.univ.filter (fun g : ZMod 2 × ZMod 2 × ZMod (2 ^ e) => g + g = 0)) =
      (Finset.univ : Finset (ZMod 2)) ×ˢ ((Finset.univ : Finset (ZMod 2)) ×ˢ
        (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0))) := by
    ext ⟨a, b, c⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, Prod.mk_add_mk, Prod.mk_eq_zero]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b, h⟩
  rw [this, Finset.card_product, Finset.card_product, gl2b2_twoTors e he]
  simp

/- English proof (translation)
Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds`. Introduce `ε hε`. Establish `hε' : ε ≠ 0` using `ne_of_gt hε`. Use `⟨max 2 ((4:ℝ) ^ (3 / ε)), ?_⟩` and prove the remaining obligations. Introduce `x hx y lam hy hlam hlamle`.

Establish `hx2 : 2 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx4 : (4:ℝ) ^ (3 / ε) ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `ht4 : 4 ≤ x ^ (ε / 3)`. Establish `h1 : ((4:ℝ) ^ (3 / ε)) ^ (ε / 3) ≤ x ^ (ε / 3)` using `Real.rpow_le_rpow (by positivity) hx4 (by positivity)`.

Rewrite `h1` using `[← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]`. Apply the tactic sequence `have h3 : 3 / ε * (ε / 3) = 1 := by field_simp <;> ring`. Rewrite `h1` using `[h3, Real.rpow_one]`. Conclude with `h1`. Establish `hL : 0 < Real.log x` using `Real.log_pos (by linarith)`.

Establish `hLne : Real.log x ≠ 0` using `ne_of_gt hL`. Establish `hypos : 0 < y` using `lt_of_lt_of_le (by positivity) hy`. Establish `hlog3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y`. Rewrite using `[← Real.exp_le_exp, Real.exp_log hypos, Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 3)]`. Conclude with `hy`. Establish `ha : x ^ (ε / 3) / 2 ≤ Real.log y` using `by linarith`. Use `⟨ha, ?_, ?_⟩` and prove the remaining obligations.

Establish `hsplit : x ^ (ε / 3) = x ^ (2 * ε / 15) * x ^ (ε / 5)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[le_div_iff₀ hlam]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : x ^ (ε / 3) = x ^ (ε / 6) * x ^ (ε / 6)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs : 0 ≤ x ^ (ε / 6) / 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `h5 : (x ^ (ε / 6) / 2) ^ 2 = x ^ (ε / 3) / 4` using `by rw [hsplit]; ring`. Rewrite using `[h5]`.

Establish `: 0 ≤ x ^ (ε / 3)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem numerical_nonvanishing_bound : Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds
  intro ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  refine ⟨max 2 ((4:ℝ) ^ (3 / ε)), ?_⟩
  intro x hx y lam hy hlam hlamle
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hx4 : (4:ℝ) ^ (3 / ε) ≤ x := le_trans (le_max_right _ _) hx
  have ht4 : 4 ≤ x ^ (ε / 3) := by
    have h1 : ((4:ℝ) ^ (3 / ε)) ^ (ε / 3) ≤ x ^ (ε / 3) :=
      Real.rpow_le_rpow (by positivity) hx4 (by positivity)
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)] at h1
    have h3 : 3 / ε * (ε / 3) = 1 := by field_simp <;> ring
    rw [h3, Real.rpow_one] at h1
    exact h1
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLne : Real.log x ≠ 0 := ne_of_gt hL
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y := by
    rw [← Real.exp_le_exp, Real.exp_log hypos, Real.exp_sub,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    exact hy
  have ha : x ^ (ε / 3) / 2 ≤ Real.log y := by linarith
  refine ⟨ha, ?_, ?_⟩
  · have hsplit : x ^ (ε / 3) = x ^ (2 * ε / 15) * x ^ (ε / 5) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [le_div_iff₀ hlam]
    calc x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * lam
        ≤ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * (2 * x ^ (ε / 5) * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlamle (by positivity)
      _ = x ^ (ε / 3) / 2 := by rw [hsplit]; field_simp <;> ring
      _ ≤ Real.log y := ha
  · have hsplit : x ^ (ε / 3) = x ^ (ε / 6) * x ^ (ε / 6) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hs : 0 ≤ x ^ (ε / 6) / 2 := by positivity
    calc x ^ (ε / 6) / 2 = Real.sqrt ((x ^ (ε / 6) / 2) ^ 2) := (Real.sqrt_sq hs).symm
      _ ≤ Real.sqrt (Real.log y) := by
          apply Real.sqrt_le_sqrt
          have h5 : (x ^ (ε / 6) / 2) ^ 2 = x ^ (ε / 3) / 4 := by rw [hsplit]; ring
          rw [h5]
          have : 0 ≤ x ^ (ε / 3) := by positivity
          linarith

/- English proof (translation)
Conclude with `integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb`.
-/
private lemma gl2b2_intH (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (39 / 100 : ℝ)))
      (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb

/- English proof (translation)
Establish `hv0 : 0 < v` using `by linarith`. Establish `h61 : v ^ (61 / 100 : ℝ) ≤ v`. Combine the equalities or inequalities in the displayed calculation. Establish `hlv : lam ≤ v` using `le_trans hl h61`. Establish `hsq : Real.sqrt v ≤ v ^ (61 / 100 : ℝ)`.

Rewrite using `[Real.sqrt_eq_rpow]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hv (by norm_num)`. Establish `hsplit : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v`. Rewrite using `[← Real.rpow_add hv0]`. Evaluate the numerical expressions.

Establish `hD : 0 < lam + Real.sqrt v` using `by positivity`. Establish `h39 : 0 ≤ v ^ (39 / 100 : ℝ)` using `by positivity`. Establish `hkey : v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v) ≤ 2 * v`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl h39, mul_le_mul_of_nonneg_left hsq h39]`. Establish `hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ hD]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hkey hc.le]`. Establish `hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ)`. Rewrite using `[Real.rpow_two]`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hlv) hv0.le, mul_nonneg (sub_nonneg.mpr hlv) hl0.le]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma gl2b2_ptw (c v lam : ℝ) (hc : 0 < c) (hv : 1 ≤ v) (hl0 : 0 < lam)
    (hl : lam ≤ v ^ (61 / 100 : ℝ)) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have h61 : v ^ (61 / 100 : ℝ) ≤ v := by
    calc v ^ (61 / 100 : ℝ) ≤ v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
      _ = v := Real.rpow_one v
  have hlv : lam ≤ v := le_trans hl h61
  have hsq : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hsplit : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv0]; norm_num
  have hD : 0 < lam + Real.sqrt v := by positivity
  have h39 : 0 ≤ v ^ (39 / 100 : ℝ) := by positivity
  have hkey : v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v) ≤ 2 * v := by
    nlinarith [mul_le_mul_of_nonneg_left hl h39, mul_le_mul_of_nonneg_left hsq h39]
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hkey hc.le]
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlv) hv0.le, mul_nonneg (sub_nonneg.mpr hlv) hl0.le]
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by ring

/- English proof (translation)
Use `⟨max 1 (|M| ^ (1 / a)), le_max_left _ _, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h2 : |M| ^ (1 / a) ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `h3 : (|M| ^ (1 / a)) ^ a ≤ x ^ a` using `Real.rpow_le_rpow (by positivity) h2 ha.le`. Rewrite `h3` using `[← Real.rpow_mul (abs_nonneg M), one_div_mul_cancel ha.ne', Real.rpow_one]`. Conclude with `le_trans (le_abs_self M) h3`.
-/
private lemma gl2b2_big_lemma {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → M ≤ x ^ a := by
  refine ⟨max 1 (|M| ^ (1 / a)), le_max_left _ _, fun x hx => ?_⟩
  have h2 : |M| ^ (1 / a) ≤ x := le_trans (le_max_right _ _) hx
  have h3 : (|M| ^ (1 / a)) ^ a ≤ x ^ a :=
    Real.rpow_le_rpow (by positivity) h2 ha.le
  rw [← Real.rpow_mul (abs_nonneg M), one_div_mul_cancel ha.ne', Real.rpow_one] at h3
  exact le_trans (le_abs_self M) h3

/- English proof (translation)
Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral`. Introduce `ε c hε hc`. Use `set I : ℝ := ∫ v in Set.Ioi 0, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hI`. Establish `hIint` using `gl2b2_intH (c / 4) (by positivity)`. Establish `hI0 : 0 ≤ I`.

Apply `MeasureTheory.setIntegral_nonneg measurableSet_Ioi` to reduce the goal to its premises. Introduce `v hv`. Establish `: 0 < v` using `hv`. Check the signs of the components of the expression. Use `set δ : ℝ := 13 * ε / 20000 with hδ`.

Use `set δ' : ℝ := 13 * ε / 40000 with hδ'`. Establish `hδpos : 0 < δ` using `by positivity`. Establish `hδ'pos : 0 < δ'` using `by positivity`. Take `⟨X1, -, hX1'⟩` from `gl2b2_big_lemma (a := ε / 300) (by positivity) 2`. Take `⟨X2, -, hX2'⟩` from `gl2b2_big_lemma (a := ε / 8) (by positivity) (32 * I / c)`.

Take `⟨X3, -, hX3'⟩` from `gl2b2_big_lemma (a := δ) hδpos (2 / δ' ^ 2)`. Use `⟨c / 8, max (max X1 X2) (max X3 2), by positivity, ?_⟩` and prove the remaining obligations. Introduce `x hx V lam hV hlam1 hlam`. Establish `hx1 : X1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hx2 : X2 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`.

Establish `hx3 : X3 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hx4 : (2:ℝ) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hxone : 1 ≤ x` using `by linarith`. Establish `hVx : x ^ (33 * ε / 100) ≤ V`.

Establish `h1` using `hX1' x hx1`. Establish `hs : x ^ (ε / 3) = x ^ (33 * ε / 100) * x ^ (ε / 300)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpos : 0 ≤ x ^ (33 * ε / 100)` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 hpos]`. Establish `hV1 : 1 ≤ V` using `le_trans (Real.one_le_rpow hxone (by positivity)) hVx`. Establish `hV0 : 0 < V` using `by linarith`. Establish `hL0 : 0 < Real.log x` using `Real.log_pos (by linarith)`.

Establish `hLle : Real.log x ≤ x ^ δ' / δ'`. Establish `h` using `Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 δ')`. Rewrite `h` using `[Real.log_rpow hx0]`. Rewrite using `[le_div_iff₀ hδ'pos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL2 : Real.log x ^ 2 ≤ x ^ δ / δ' ^ 2`. Establish `hsq : x ^ δ = x ^ δ' * x ^ δ'`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Rewrite using `[hδ, hδ']`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hLle) hL0.le, mul_nonneg (sub_nonneg.mpr hLle) (sub_nonneg.mpr hLle)]`. Rewrite using `[hsq]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlamV : lam ≤ V ^ (61 / 100 : ℝ)`. Establish `h1 : (x ^ (33 * ε / 100)) ^ (61 / 100 : ℝ) ≤ V ^ (61 / 100 : ℝ)` using `Real.rpow_le_rpow (by positivity) hVx (by norm_num)`. Rewrite `h1` using `[← Real.rpow_mul hx0.le]`. Establish `hs : x ^ (33 * ε / 100 * (61 / 100)) = x ^ (ε / 5) * x ^ δ * x ^ δ`. Rewrite using `[← Real.rpow_add hx0, ← Real.rpow_add hx0]`.

Use `congr 1`. Rewrite using `[hδ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[hs]`. Establish `h3` using `hX3' x hx3`.

Establish `h4 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2)` using `mul_le_mul_of_nonneg_left hL2 (by positivity)`. Establish `h5 : 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) = x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2)` using `by ring`. Establish `h6 : x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) ≤ x ^ (ε / 5) * x ^ δ * x ^ δ` using `mul_le_mul_of_nonneg_left h3 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))`.

Introduce `v hv`. Establish `hv' : V < v` using `hv`. Establish `hv1 : 1 ≤ v` using `by linarith`. Establish `hlv : lam ≤ v ^ (61 / 100 : ℝ)` using `le_trans hlamV (Real.rpow_le_rpow hV0.le hv'.le (by norm_num))`. Establish `h1` using `gl2b2_ptw c v lam hc hv1 (by linarith) hlv`.

Establish `h39 : V ^ (39 / 100 : ℝ) ≤ v ^ (39 / 100 : ℝ)` using `Real.rpow_le_rpow hV0.le hv'.le (by norm_num)`. Establish `h2 : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤ Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h39 hc.le]`.

Establish `hv2 : 0 ≤ v ^ (2 : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hgint : MeasureTheory.IntegrableOn (fun v : ℝ => 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) (Set.Ioi V)` using `(hIint.mono_set (Set.Ioi_subset_Ioi hV0.le)).const_mul _`. Establish `hFmeas : MeasureTheory.AEStronglyMeasurable (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (MeasureTheory.volume.restrict (Set.Ioi V))`. Apply `Measurable.aestronglyMeasurable` to reduce the goal to its premises.

Use `fun_prop`. Establish `hFint : MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V)`. Use `MeasureTheory.Integrable.mono' hgint hFmeas ?_` and prove the remaining obligations. Use `MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_` and prove the remaining obligations. Introduce `v hv`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `hpt v hv`. Use `⟨hFint, ?_⟩` and prove the remaining obligations. Establish `hw : x ^ (ε / 8) ≤ V ^ (39 / 100 : ℝ)`. Establish `h1 : (x ^ (33 * ε / 100)) ^ (39 / 100 : ℝ) ≤ V ^ (39 / 100 : ℝ)` using `Real.rpow_le_rpow (by positivity) hVx (by norm_num)`.

Rewrite `h1` using `[← Real.rpow_mul hx0.le]`. Use `le_trans (Real.rpow_le_rpow_of_exponent_le hxone ?_) h1` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hInt_le : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[hI]`. Apply `MeasureTheory.setIntegral_mono_set hIint` to reduce the goal to its premises. Use `MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_` and prove the remaining obligations. Introduce `v hv`.

Establish `: 0 < v` using `hv`. Use `show (0:ℝ) ≤ _`. Check the signs of the components of the expression. Conclude with `(Set.Ioi_subset_Ioi hV0.le).eventuallyLE`. Establish `hw2 : 32 * I / c ≤ x ^ (ε / 8)` using `hX2' x hx2`.

Establish `h4I : 4 * I ≤ Real.exp (c / 8 * x ^ (ε / 8))`. Establish `h1` using `Real.add_one_le_exp (c / 8 * x ^ (ε / 8))`. Establish `h2 : 4 * I ≤ c / 8 * x ^ (ε / 8)`. Rewrite `hw2` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE1 : Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) ≤ Real.exp (-(c / 4) * x ^ (ε / 8))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hw hc.le]`. Establish `hsplitE : Real.exp (-(c / 4) * x ^ (ε / 8)) = (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8))`.

Rewrite using `[← Real.exp_neg, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsplitE]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Real.exp (c / 8 * x ^ (ε / 8)) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4I (by positivity)) (Real.exp_pos _).le`. Use `_ = Real.exp (-(c / 8) * x ^ (ε / 8)) := by`. Rewrite using `[mul_inv_cancel₀ (Real.exp_pos _).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gl2b2_thinIntegral : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral
  intro ε c hε hc
  set I : ℝ := ∫ v in Set.Ioi 0, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hI
  have hIint := gl2b2_intH (c / 4) (by positivity)
  have hI0 : 0 ≤ I := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro v hv
    have : 0 < v := hv
    positivity
  set δ : ℝ := 13 * ε / 20000 with hδ
  set δ' : ℝ := 13 * ε / 40000 with hδ'
  have hδpos : 0 < δ := by positivity
  have hδ'pos : 0 < δ' := by positivity
  obtain ⟨X1, -, hX1'⟩ := gl2b2_big_lemma (a := ε / 300) (by positivity) 2
  obtain ⟨X2, -, hX2'⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (32 * I / c)
  obtain ⟨X3, -, hX3'⟩ := gl2b2_big_lemma (a := δ) hδpos (2 / δ' ^ 2)
  refine ⟨c / 8, max (max X1 X2) (max X3 2), by positivity, ?_⟩
  intro x hx V lam hV hlam1 hlam
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hVx : x ^ (33 * ε / 100) ≤ V := by
    have h1 := hX1' x hx1
    have hs : x ^ (ε / 3) = x ^ (33 * ε / 100) * x ^ (ε / 300) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hpos : 0 ≤ x ^ (33 * ε / 100) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos]
  have hV1 : 1 ≤ V := le_trans (Real.one_le_rpow hxone (by positivity)) hVx
  have hV0 : 0 < V := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLle : Real.log x ≤ x ^ δ' / δ' := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 δ')
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hδ'pos]
    linarith
  have hL2 : Real.log x ^ 2 ≤ x ^ δ / δ' ^ 2 := by
    have hsq : x ^ δ = x ^ δ' * x ^ δ' := by
      rw [← Real.rpow_add hx0]; congr 1; rw [hδ, hδ']; ring
    have h2 : Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLle) hL0.le,
        mul_nonneg (sub_nonneg.mpr hLle) (sub_nonneg.mpr hLle)]
    rw [hsq]
    calc Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := h2
      _ = x ^ δ' * x ^ δ' / δ' ^ 2 := by ring
  have hlamV : lam ≤ V ^ (61 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (61 / 100 : ℝ) ≤ V ^ (61 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    have hs : x ^ (33 * ε / 100 * (61 / 100)) = x ^ (ε / 5) * x ^ δ * x ^ δ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; rw [hδ]; ring
    rw [hs] at h1
    have h3 := hX3' x hx3
    have h4 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h5 : 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) = x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) := by ring
    have h6 : x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) ≤ x ^ (ε / 5) * x ^ δ * x ^ δ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
        (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) := by
    intro v hv
    have hv' : V < v := hv
    have hv1 : 1 ≤ v := by linarith
    have hlv : lam ≤ v ^ (61 / 100 : ℝ) :=
      le_trans hlamV (Real.rpow_le_rpow hV0.le hv'.le (by norm_num))
    have h1 := gl2b2_ptw c v lam hc hv1 (by linarith) hlv
    have h39 : V ^ (39 / 100 : ℝ) ≤ v ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow hV0.le hv'.le (by norm_num)
    have h2 : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤
        Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h39 hc.le]
    have hv2 : 0 ≤ v ^ (2 : ℝ) := by positivity
    calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
        ≤ 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := h1
      _ ≤ 4 * (v ^ (2 : ℝ) * (Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hv2) (by norm_num)
      _ = _ := by ring
  have hgint : MeasureTheory.IntegrableOn (fun v : ℝ => 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
      (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) (Set.Ioi V) :=
    (hIint.mono_set (Set.Ioi_subset_Ioi hV0.le)).const_mul _
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      (MeasureTheory.volume.restrict (Set.Ioi V)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hFint : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgint hFmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hFint, ?_⟩
  have hw : x ^ (ε / 8) ≤ V ^ (39 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (39 / 100 : ℝ) ≤ V ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hxone ?_) h1
    linarith
  have hInt_le : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
    calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
        ≤ ∫ v in Set.Ioi V, 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) :=
          MeasureTheory.setIntegral_mono_on hFint hgint measurableSet_Ioi hpt
      _ = 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            ∫ v in Set.Ioi V, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hI]
          apply MeasureTheory.setIntegral_mono_set hIint
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
            intro v hv
            have : 0 < v := hv
            show (0:ℝ) ≤ _
            positivity
          · exact (Set.Ioi_subset_Ioi hV0.le).eventuallyLE
  have hw2 : 32 * I / c ≤ x ^ (ε / 8) := hX2' x hx2
  have h4I : 4 * I ≤ Real.exp (c / 8 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c / 8 * x ^ (ε / 8))
    have h2 : 4 * I ≤ c / 8 * x ^ (ε / 8) := by
      rw [div_le_iff₀ hc] at hw2
      linarith
    linarith
  have hE1 : Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) ≤ Real.exp (-(c / 4) * x ^ (ε / 8)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw hc.le]
  have hsplitE : Real.exp (-(c / 4) * x ^ (ε / 8)) =
      (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := hInt_le
    _ ≤ 4 * Real.exp (-(c / 4) * x ^ (ε / 8)) * I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1 (by norm_num)) hI0
    _ = (4 * I) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [hsplitE]; ring
    _ ≤ Real.exp (c / 8 * x ^ (ε / 8)) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ *
          Real.exp (-(c / 8) * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4I (by positivity))
          (Real.exp_pos _).le
    _ = Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [mul_inv_cancel₀ (Real.exp_pos _).ne']; ring

/- English proof (translation)
Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound`. Introduce `ε c C hε hc hC`. Take `⟨c0, X0, hc0, hX0⟩` from `gl2b2_thinIntegral ε c hε hc`. Take `⟨XN, hXN⟩` from `numerical_nonvanishing_bound ε hε`. Take `⟨XW, -, hXW⟩` from `gl2b2_big_lemma (a := ε / 8) (by positivity) (2 * C / c0)`.

Use `⟨c0 / 2, max (max X0 XN) XW, by positivity, ?_⟩` and prove the remaining obligations. Introduce `x hx y lam psi0 hy hlam1 hlam hpsi`. Establish `hxX0 : X0 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxN : XN ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxW : XW ≤ x` using `le_trans (le_max_right _ _) hx`.

Take `⟨hV, -, -⟩` from `hXN x hxN y lam hy (by linarith) hlam`. Take `⟨hGint, hGle⟩` from `hX0 x hxX0 (Real.log y) lam hV hlam1 hlam`. Establish `hypos : 0 < y` using `lt_of_lt_of_le (by positivity) hy`. Use `set G : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hGdef`. Establish `himg : Real.log '' Set.Ioi y = Set.Ioi (Real.log y)`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `Real.log_lt_log hypos hu`. Introduce `hv`.

Use `⟨Real.exp v, ?_, Real.log_exp v⟩` and prove the remaining obligations. Establish `h1 : Real.exp (Real.log y) < Real.exp v` using `Real.exp_lt_exp.mpr hv`. Rewrite `h1` using `[Real.exp_log hypos]`. Then use the resulting hypothesis. Establish `hderiv : ∀ u ∈ Set.Ioi y, HasDerivWithinAt Real.log u⁻¹ (Set.Ioi y) u`. Introduce `u hu`.

Establish `hu0 : 0 < u` using `lt_trans hypos hu`. Conclude with `(Real.hasDerivAt_log hu0.ne').hasDerivWithinAt`. Establish `hinj : Set.InjOn Real.log (Set.Ioi y)` using `Real.log_injOn_pos.mono (Set.Ioi_subset_Ioi hypos.le)`. Establish `hHint : MeasureTheory.IntegrableOn (fun u : ℝ => |u⁻¹| • G (Real.log u)) (Set.Ioi y)` using `(MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj G).mp (by rw [himg]; exact hGint)`. Establish `hHeq : (∫ u in Set.Ioi y, |u⁻¹| • G (Real.log u)) = ∫ v in Set.Ioi (Real.log y), G v`.

Establish `h1` using `MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj G`. Rewrite `h1` using `[himg]`. Conclude with `h1.symm`. Establish `hbound : ∀ u ∈ Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * (|u⁻¹| • G (Real.log u))`. Introduce `u hu`.

Establish `hu0 : 0 < u` using `lt_trans hypos hu`. Establish `hu0' : u ≠ 0` using `hu0.ne'`. Establish `h1` using `hpsi u (le_of_lt hu)`. Rewrite using `[norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, abs_of_pos (inv_pos.mpr hu0), smul_eq_mul, div_le_iff₀ (by positivity)]`. Establish `hG : G (Real.log u) = (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))` using `rfl`.

Establish `hu2 : u⁻¹ * u ^ 2 = u`. Rewrite using `[pow_two, ← mul_assoc, inv_mul_cancel₀ hu0', one_mul]`. Rewrite using `[hG]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show C * (u⁻¹ * ((Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 = C * ((Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) * (u⁻¹ * u ^ 2) by ring, hu2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ ∫ u in Set.Ioi y, C * (|u⁻¹| • G (Real.log u))` using `MeasureTheory.norm_integral_le_of_norm_le (hHint.const_mul C) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)`. Rewrite `hnorm` using `[MeasureTheory.integral_const_mul, hHeq]`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]`. Use `mul_le_mul_of_nonneg_left ?_ hypos.le` and prove the remaining obligations.

Establish `hw` using `hXW x hxW`. Establish `hCexp : C ≤ Real.exp (c0 / 2 * x ^ (ε / 8))`. Establish `h1` using `Real.add_one_le_exp (c0 / 2 * x ^ (ε / 8))`. Rewrite `hw` using `[div_le_iff₀ hc0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem nonvanishing_of_hypothesis : Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound
  intro ε c C hε hc hC
  obtain ⟨c0, X0, hc0, hX0⟩ := gl2b2_thinIntegral ε c hε hc
  obtain ⟨XN, hXN⟩ := numerical_nonvanishing_bound ε hε
  obtain ⟨XW, -, hXW⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (2 * C / c0)
  refine ⟨c0 / 2, max (max X0 XN) XW, by positivity, ?_⟩
  intro x hx y lam psi0 hy hlam1 hlam hpsi
  have hxX0 : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxN : XN ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxW : XW ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hV, -, -⟩ := hXN x hxN y lam hy (by linarith) hlam
  obtain ⟨hGint, hGle⟩ := hX0 x hxX0 (Real.log y) lam hV hlam1 hlam
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  set G : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hGdef
  have himg : Real.log '' Set.Ioi y = Set.Ioi (Real.log y) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.log_lt_log hypos hu
    · intro hv
      refine ⟨Real.exp v, ?_, Real.log_exp v⟩
      have h1 : Real.exp (Real.log y) < Real.exp v := Real.exp_lt_exp.mpr hv
      rwa [Real.exp_log hypos] at h1
  have hderiv : ∀ u ∈ Set.Ioi y, HasDerivWithinAt Real.log u⁻¹ (Set.Ioi y) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    exact (Real.hasDerivAt_log hu0.ne').hasDerivWithinAt
  have hinj : Set.InjOn Real.log (Set.Ioi y) :=
    Real.log_injOn_pos.mono (Set.Ioi_subset_Ioi hypos.le)
  have hHint : MeasureTheory.IntegrableOn (fun u : ℝ => |u⁻¹| • G (Real.log u)) (Set.Ioi y) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G).mp (by rw [himg]; exact hGint)
  have hHeq : (∫ u in Set.Ioi y, |u⁻¹| • G (Real.log u)) = ∫ v in Set.Ioi (Real.log y), G v := by
    have h1 := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G
    rw [himg] at h1
    exact h1.symm
  have hbound : ∀ u ∈ Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * (|u⁻¹| • G (Real.log u)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    have hu0' : u ≠ 0 := hu0.ne'
    have h1 := hpsi u (le_of_lt hu)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      abs_of_pos (inv_pos.mpr hu0), smul_eq_mul, div_le_iff₀ (by positivity)]
    have hG : G (Real.log u) = (Real.log u + lam) ^ 2 *
        Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := rfl
    have hu2 : u⁻¹ * u ^ 2 = u := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hu0', one_mul]
    rw [hG]
    calc ‖psi0 u‖ ≤ C * u * (Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := h1
      _ = C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 := by
        rw [show C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 =
          C * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) * (u⁻¹ * u ^ 2) by ring,
          hu2]
        ring
  have hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤
      ∫ u in Set.Ioi y, C * (|u⁻¹| • G (Real.log u)) :=
    MeasureTheory.norm_integral_le_of_norm_le (hHint.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  rw [MeasureTheory.integral_const_mul, hHeq] at hnorm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
  refine mul_le_mul_of_nonneg_left ?_ hypos.le
  have hw := hXW x hxW
  have hCexp : C ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c0 / 2 * x ^ (ε / 8))
    rw [div_le_iff₀ hc0] at hw
    linarith
  calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ v in Set.Ioi (Real.log y), G v := hnorm
    _ ≤ C * Real.exp (-c0 * x ^ (ε / 8)) := mul_le_mul_of_nonneg_left hGle hC.le
    _ ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) * Real.exp (-c0 * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
    _ = Real.exp (-(c0 / 2) * x ^ (ε / 8)) := by rw [← Real.exp_add]; congr 1; ring

/- English proof (translation)
Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate`. Introduce `ε c C hε hc hC`. Take `⟨c', x₀, hc', h⟩` from `nonvanishing_of_hypothesis ε c C hε hc hC`. Use `⟨c', x₀, hc', ?_⟩` and prove the remaining obligations. Introduce `x hx y lam hy h1 h2`.

Prove the components needed by the constructor for the conclusion. Introduce `N _ χ hG hb`. Rewrite using `[hG, norm_neg]`. Conclude with `h x hx y lam _ hy h1 h2 hb`. Introduce `hG hb`.

Rewrite using `[hG, abs_neg]`. Establish `h3` using `h x hx y lam (fun u => ((Chebyshev.psi u - u : ℝ) : ℂ)) hy h1 h2 (by intro u hu; simp only [Complex.norm_real, Real.norm_eq_abs]; exact hb u hu)`. Establish `hcast : ((y : ℂ) * ∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) = ((y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ)`. Establish `h4 : (∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) = ∫ u in Set.Ioi y, (((Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ)`. Use `congr 1`.

Use extensionality with `u`. Use `push_cast`. Apply the tactic sequence `try ring`. Rewrite using `[h4, Complex.ofReal_mul]`. Use `congr 1`.

Use `first`. Consider the case `exact MeasureTheory.integral_ofReal`. Consider the case `exact integral_ofReal`. Consider the case `exact integral_complex_ofReal`. Rewrite `h3` using `[hcast, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `h3`.
-/
theorem character_estimate_of_hypothesis : Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate
  intro ε c C hε hc hC
  obtain ⟨c', x₀, hc', h⟩ := nonvanishing_of_hypothesis ε c C hε hc hC
  refine ⟨c', x₀, hc', ?_⟩
  intro x hx y lam hy h1 h2
  constructor
  · intro N _ χ hG hb
    rw [hG, norm_neg]
    exact h x hx y lam _ hy h1 h2 hb
  · intro hG hb
    rw [hG, abs_neg]
    have h3 := h x hx y lam (fun u => ((Chebyshev.psi u - u : ℝ) : ℂ)) hy h1 h2
      (by intro u hu; simp only [Complex.norm_real, Real.norm_eq_abs]; exact hb u hu)
    have hcast : ((y : ℂ) * ∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
        ((y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
      have h4 : (∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
          ∫ u in Set.Ioi y, (((Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
        congr 1
        ext u
        push_cast
        try ring
      rw [h4, Complex.ofReal_mul]
      congr 1
      first
        | exact MeasureTheory.integral_ofReal
        | exact integral_ofReal
        | exact integral_complex_ofReal
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h3
    exact h3

end Formalism.HermitianLattices.ZeroFreeRegionGL2
