import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Establish `hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u` using `by ring`. Rewrite using `[hid]`. Establish `h1 : 0 ≤ (c - ρ) * (Ah - ρ)` using `mul_nonneg (by linarith) (by linarith)`. Establish `h2 : 0 ≤ ρ * u` using `mul_nonneg hρ0 hu0`. Establish `hcA : 0 < c * Ah` using `mul_pos hc hA`.

Break down `le_total c Ah with h | h` into its components or cases. Rewrite `hu` using `[max_eq_right h]`. Break down `le_total (c / 2) ρ with h3 | h3` into its components or cases. Establish `: c / 2 * (2 * τ * Ah) ≤ ρ * u` using `mul_le_mul h3 hu.le (by positivity) hρ0`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ)` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hu` using `[max_eq_left h]`. Break down `le_total (Ah / 2) ρ with h3 | h3` into its components or cases. Establish `: Ah / 2 * (2 * τ * c) ≤ ρ * u` using `mul_le_mul h3 hu.le (by positivity) hρ0`.

Use the polynomial consequences of the given equalities and inequalities. Establish `: c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ)` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nk_vi (c Ah ρ u τ : ℝ) (hc : 0 < c) (hA : 0 < Ah) (hρ0 : 0 ≤ ρ) (hρc : ρ ≤ c) (hρA : ρ ≤ Ah) (hu0 : 0 ≤ u)
    (hτ0 : 0 < τ) (hτ : τ < 1 / 4) (hu : 2 * τ * max c Ah < u) : ρ * (c + Ah - u - ρ) ≤ (1 - τ) * (c * Ah) := by
  have hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u := by ring
  rw [hid]
  have h1 : 0 ≤ (c - ρ) * (Ah - ρ) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ρ * u := mul_nonneg hρ0 hu0
  have hcA : 0 < c * Ah := mul_pos hc hA
  rcases le_total c Ah with h | h
  · rw [max_eq_right h] at hu
    rcases le_total (c / 2) ρ with h3 | h3
    · have : c / 2 * (2 * τ * Ah) ≤ ρ * u := mul_le_mul h3 hu.le (by positivity) hρ0
      nlinarith
    · have : c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ) := mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      nlinarith
  · rw [max_eq_left h] at hu
    rcases le_total (Ah / 2) ρ with h3 | h3
    · have : Ah / 2 * (2 * τ * c) ≤ ρ * u := mul_le_mul h3 hu.le (by positivity) hρ0
      nlinarith
    · have : c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ) := mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      nlinarith

/- English proof (translation)
Establish `hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u` using `by ring`. Rewrite using `[hid]`. Establish `h1 : 0 ≤ (c - ρ) * (Ah - ρ)` using `mul_nonneg (by linarith) (by linarith)`. Establish `h2 : 0 ≤ ρ * u` using `mul_nonneg hρ0 hu0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nk_iv (c Ah ρ u : ℝ) (hρ0 : 0 ≤ ρ) (hρc : ρ ≤ c) (hρA : ρ ≤ Ah) (hu0 : 0 ≤ u) :
    ρ * (c + Ah - u - ρ) ≤ c * Ah := by
  have hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u := by ring
  rw [hid]
  have h1 : 0 ≤ (c - ρ) * (Ah - ρ) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ρ * u := mul_nonneg hρ0 hu0
  linarith

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]`. Establish `ih'` using `ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => hx _) (fun i => hy _) (fun i => by simpa using h i.castSucc)`.

Establish `hl` using `h (Fin.last s)`. Simplify using `only [Fin.val_last] at hl`. Establish `hp : 0 ≤ ∏ i : Fin s, x i.castSucc` using `Finset.prod_nonneg fun i _ => hx _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nk_tele (s : ℕ) (c : ℕ → ℝ) (x y : Fin s → ℝ) (hc : ∀ l, 0 ≤ c l) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h : ∀ i : Fin s, x i * c (i + 1) ≤ y i * c i) : c s * ∏ i, x i ≤ c 0 * ∏ i, y i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have ih' := ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => hx _) (fun i => hy _)
      (fun i => by simpa using h i.castSucc)
    have hl := h (Fin.last s)
    simp only [Fin.val_last] at hl
    have hp : 0 ≤ ∏ i : Fin s, x i.castSucc := Finset.prod_nonneg fun i _ => hx _
    calc c (s + 1) * ((∏ i : Fin s, x i.castSucc) * x (Fin.last s))
        = (∏ i : Fin s, x i.castSucc) * (x (Fin.last s) * c (s + 1)) := by ring
      _ ≤ (∏ i : Fin s, x i.castSucc) * (y (Fin.last s) * c s) := mul_le_mul_of_nonneg_left hl hp
      _ = y (Fin.last s) * (c s * ∏ i : Fin s, x i.castSucc) := by ring
      _ ≤ y (Fin.last s) * (c 0 * ∏ i : Fin s, y i.castSucc) := mul_le_mul_of_nonneg_left ih' (hy _)
      _ = _ := by ring

/- English proof (translation)
Establish `h1` using `nk_tele s c x (fun i => κ i * (E2 * Ai i)) hc hx (fun i => by have := hκ i; have := hAi i; positivity) hstep`. Establish `hpx : 0 ≤ ∏ i, x i` using `Finset.prod_nonneg fun i _ => hx i`. Establish `hpn : 0 ≤ ∏ i, nn i` using `Finset.prod_nonneg fun i _ => hn0 i`. Establish `hpy : 0 ≤ ∏ i, (κ i * (E2 * Ai i))` using `Finset.prod_nonneg fun i _ => by have := hκ i; have := hAi i; positivity`. Establish `h2 : ∏ i, nn i ≤ ∏ i, (μ i * (E2 * Ci i))` using `Finset.prod_le_prod (fun i _ => hn0 i) fun i _ => hn i`.

Establish `e1 : ∏ i, (κ i * (E2 * Ai i)) = (∏ i, κ i) * (E2 ^ s * ∏ i, Ai i)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `e2 : ∏ i, (μ i * (E2 * Ci i)) = (∏ i, μ i) * (E2 ^ s * ∏ i, Ci i)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nk_bracket (s : ℕ) (c : ℕ → ℝ) (x nn Ai Ci κ μ : Fin s → ℝ) (l A E1 E2 : ℝ)
    (hc : ∀ l, 0 ≤ c l) (hx : ∀ i, 0 ≤ x i) (hn0 : ∀ i, 0 ≤ nn i) (hAi : ∀ i, 0 ≤ Ai i) (hCi : ∀ i, 0 ≤ Ci i)
    (hκ : ∀ i, 0 ≤ κ i) (hμ : ∀ i, 0 ≤ μ i) (hl0 : 0 ≤ l) (hE2 : 0 ≤ E2)
    (hstep : ∀ i : Fin s, x i * c (i + 1) ≤ (κ i * (E2 * Ai i)) * c i)
    (hl : l ≤ c s) (hn : ∀ i, nn i ≤ μ i * (E2 * Ci i)) (hA : c 0 ≤ E1 * A) :
    l * (∏ i, x i) * (∏ i, nn i) ≤
      (E1 * E2 ^ s * E2 ^ s * ((∏ i, κ i) * ∏ i, μ i)) * (A * (∏ i, Ai i) * ∏ i, Ci i) := by
  have h1 := nk_tele s c x (fun i => κ i * (E2 * Ai i)) hc hx (fun i => by have := hκ i; have := hAi i; positivity) hstep
  have hpx : 0 ≤ ∏ i, x i := Finset.prod_nonneg fun i _ => hx i
  have hpn : 0 ≤ ∏ i, nn i := Finset.prod_nonneg fun i _ => hn0 i
  have hpy : 0 ≤ ∏ i, (κ i * (E2 * Ai i)) :=
    Finset.prod_nonneg fun i _ => by have := hκ i; have := hAi i; positivity
  have h2 : ∏ i, nn i ≤ ∏ i, (μ i * (E2 * Ci i)) := Finset.prod_le_prod (fun i _ => hn0 i) fun i _ => hn i
  have e1 : ∏ i, (κ i * (E2 * Ai i)) = (∏ i, κ i) * (E2 ^ s * ∏ i, Ai i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : ∏ i, (μ i * (E2 * Ci i)) = (∏ i, μ i) * (E2 ^ s * ∏ i, Ci i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc l * (∏ i, x i) * (∏ i, nn i) ≤ (c s * ∏ i, x i) * ∏ i, nn i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hpx) hpn
    _ ≤ (c 0 * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, nn i := mul_le_mul_of_nonneg_right h1 hpn
    _ ≤ (E1 * A * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, nn i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hpy) hpn
    _ ≤ (E1 * A * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, (μ i * (E2 * Ci i)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_trans (hc 0) hA) hpy)
    _ = _ := by rw [e1, e2]; ring

/- English proof (translation)
Establish `hr9 : (9 : ℝ) ≤ (r : ℝ)` using `by exact_mod_cast hr`. Establish `hk : (10 : ℝ) ≤ (r : ℝ) + 1` using `by linarith`. Use `set k : ℝ := (r : ℝ) + 1 with hkdef`. Establish `hsr : 2 * (s : ℝ) + 1 ≤ k - 1`. Establish `: ((2 * s + 1 : ℕ) : ℝ) ≤ (r : ℝ)` using `by exact_mod_cast hs`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ((r - 1 : ℕ) : ℝ) = k - 2`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ ≤ Real.exp (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k))`. Rewrite using `[← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]`. Conclude with `mul_le_mul_of_nonneg_left hγ (by positivity)`. Establish `hb0 : 0 ≤ Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ` using `by positivity`.

Use `(pow_le_pow_left₀ hb0 hb (r - 1)).trans ?_` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul, hn]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hk0 : 0 < k` using `by linarith`. Establish `e1 : (k - 2) * (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k)) = (k - 2) * (4 * s + 1) / k ^ 2 - (k - 2) * La / (4 * k)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Establish `h1 : (k - 2) * (4 * s + 1) / k ^ 2 ≤ 2`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : La / 5 ≤ (k - 2) * La / (4 * k)`. Rewrite using `[div_le_div_iff₀ (by norm_num) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nk_exponent (s r : ℕ) (La γ : ℝ) (hr : 9 ≤ r) (hs : 2 * s + 1 ≤ r) (hLa : 0 ≤ La) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ Real.exp (-(La / (4 * ((r : ℝ) + 1))))) :
    (Real.exp (1 / ((r : ℝ) + 1) ^ 2) * Real.exp (2 / ((r : ℝ) + 1) ^ 2) ^ s * Real.exp (2 / ((r : ℝ) + 1) ^ 2) ^ s * γ) ^
      (r - 1) ≤ Real.exp (2 - La / 5) := by
  have hr9 : (9 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hk : (10 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  set k : ℝ := (r : ℝ) + 1 with hkdef
  have hsr : 2 * (s : ℝ) + 1 ≤ k - 1 := by
    have : ((2 * s + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
    push_cast at this
    linarith
  have hn : ((r - 1 : ℕ) : ℝ) = k - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hb : Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ ≤
      Real.exp (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k)) := by
    rw [← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hγ (by positivity)
  have hb0 : 0 ≤ Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ := by positivity
  refine (pow_le_pow_left₀ hb0 hb (r - 1)).trans ?_
  rw [← Real.exp_nat_mul, hn]
  apply Real.exp_le_exp.mpr
  have hk0 : 0 < k := by linarith
  have e1 : (k - 2) * (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k)) =
      (k - 2) * (4 * s + 1) / k ^ 2 - (k - 2) * La / (4 * k) := by
    field_simp
    ring
  rw [e1]
  have h1 : (k - 2) * (4 * s + 1) / k ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : La / 5 ≤ (k - 2) * La / (4 * k) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

end Formalism.MainNotions.ColumnSystems.Pf
