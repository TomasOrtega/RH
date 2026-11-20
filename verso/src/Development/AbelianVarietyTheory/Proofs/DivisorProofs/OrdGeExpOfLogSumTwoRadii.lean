import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.ExpWeightTwoRadii

variable {C : Type} [Field C] {M : ℕ}

def WtBelow (v : AddValuation C (WithTop ℝ)) (ρ : Fin M → ℝ) (D : ℕ)
    (g : MvPowerSeries (Fin M) C) (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ∑ m, ρ m * (α m : ℝ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

/- English proof (translation)
Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, Nat.cast_add, mul_add]`.
-/
theorem wt_add_index (ρ : Fin M → ℝ) (β γ : Fin M →₀ ℕ) :
    ∑ m, ρ m * ((β + γ) m : ℝ) = (∑ m, ρ m * (β m : ℝ)) + ∑ m, ρ m * (γ m : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.add_apply, Nat.cast_add, mul_add]

/- English proof (translation)
Introduce `α hα`. Rewrite using `[coeff_mul]`. Use `v.map_le_sum fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q.1 + q.2 = α` using `by simpa using hq`. Distinguish the cases in `h1 : q.1 = 0`.

Rewrite using `[h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]`. Conclude with `le_top`. Distinguish the cases in `h2 : q.2 = 0`. Rewrite using `[h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]`. Conclude with `le_top`.

Establish `hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α`. Rewrite using `[← hq', map_add]`. Establish `d1 : Finsupp.degree q.1 ≠ 0` using `fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)`. Establish `d2 : Finsupp.degree q.2 ≠ 0` using `fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)`. Rewrite using `[v.map_mul]`.

Use `le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, ← hq', wt_add_index]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem WtBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : WtBelow v ρ D g r) (hh : WtBelow v ρ D h s) :
    WtBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  by_cases h1 : q.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : q.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α := by
    rw [← hq', map_add]
  have d1 : Finsupp.degree q.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree q.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))
  rw [← WithTop.coe_add, ← hq', wt_add_index]
  congr 1
  ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hg`. Consider the case `succ k ih`. Establish `h` using `WtBelow.mul (by simp [hg0]) hg0 ih hg`. Introduce `α hα`.

Establish `h'` using `h α (by omega)`. Rewrite using `[_root_.pow_succ g (k + 1)]`. Use `le_trans (le_of_eq ?_) h'` and prove the remaining obligations. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem WtBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) (k : ℕ) :
    WtBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := WtBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, N = k + 1 + 1` from `⟨N - 2, by omega⟩`. Establish `h` using `WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg`. Rewrite using `[_root_.pow_succ g (k + 1)]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem WtBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    WtBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp1 : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `hp0 : (p : ℝ) ≠ 0` using `by linarith`. Use `set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'`. Establish `hg'1 : g' * ((p : ℝ) - 1) = 2` using `by rw [hg']; field_simp`.

Apply the tactic sequence `have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith`. Establish `hgp : 2 / ((p : ℝ) * (p - 1)) * p = g'` using `by rw [hg']; field_simp`. Establish `hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1))`. Apply the tactic sequence `apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith`. Establish `hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g'`.

Use `mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre : ∀ e, r e ≤ g'`. Apply the tactic sequence `intro e; rw [hr e]; split_ifs <;> linarith`. Establish `hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) → (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a`.

Introduce `a e n L hLg hL`. Establish `hb` using `one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n`. Establish `hb'` using `mul_le_mul_of_nonneg_left hb hg'0.le`. Establish `hb1` using `one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)`. Establish `hb1'` using `mul_le_mul_of_nonneg_left hb1 hg'0.le`.

Establish `e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n`. Take the linear combination `(n : ℝ) * hg'1`. Establish `e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1)` using `by push_cast; linear_combination ((n : ℝ) + 1) * hg'1`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hre'` using `hre e`.

Rewrite using `[hr a]`. Use `split_ifs with hga`. Establish `hL'` using `hLg hga`. Establish `e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n`. Rewrite using `[_root_.pow_succ, ← hgp]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1)` using `by ring`. Rewrite using `[e4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a)`. Introduce `D`. Proceed by induction on `D with`. Consider the case `zero => intro a α hα`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ D ih`. Introduce `e α hα`. Establish `h1 : coeff α (lgSum p c t e) = coeff α (z e)` using `by rw [hlg e]`. Establish `h2 : coeff α (lgSum p c t e) = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n))`.

Both sides reduce to the same expression. Rewrite `h1` using `[h2, Finset.sum_range_succ']`. Establish `h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e)`. Simplify using `[h0, Pi.single_apply]`. Rewrite `h1` using `[h3]`.

Rewrite using `[eq_sub_of_add_eq' h1]`. Use `v.map_le_sub (hz e α) ?_` and prove the remaining obligations. Use `v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_` and prove the remaining obligations. Establish `hN : 2 ≤ p ^ (n + 1)` using `le_trans hp.two_le (Nat.le_self_pow (by omega) p)`. Establish `h4` using `(ih a).pow (ht a) hN α hα`.

Rewrite using `[v.map_mul]`. Distinguish the cases in `hga : good a`. Establish `hc1` using `hgood a hga (n + 1) e (by omega)`. Use `le_trans ?_ (add_le_add hc1 h4)` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe]`.

Use `hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith) (by push_cast; linarith)` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc1` using `hc a (n + 1) e`. Use `le_trans ?_ (add_le_add hc1 h4)` and prove the remaining obligations.

Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe]`. Use `hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `b α`.

Conclude with `step (Finsupp.degree α + 1) b α (by omega)`.
-/
theorem ordGe_of_lgSum_radii (v : AddValuation C (WithTop ℝ)) (p : ℕ) (hp : p.Prime)
    {d : ℕ} (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C)
    (h0 : ∀ a, c a 0 = Pi.single a 1)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C) (r : Fin d → ℝ)
    (hr : ∀ b, r b = if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))
    (hz : ∀ b, OrdGe v ρ (z b) (r b)) (ht : ∀ b, constantCoeff (t b) = 0)
    (hlg : ∀ b, lgSum p c t b = z b) : ∀ b, OrdGe v ρ (t b) (r b) := by
  classical
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'
  have hg'1 : g' * ((p : ℝ) - 1) = 2 := by rw [hg']; field_simp
  have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith
  have hgp : 2 / ((p : ℝ) * (p - 1)) * p = g' := by rw [hg']; field_simp
  have hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1)) := by
    apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith
  have hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g' := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0
    linarith
  have hre : ∀ e, r e ≤ g' := by
    intro e; rw [hr e]; split_ifs <;> linarith

  have hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) →
      (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a := by
    intro a e n L hLg hL
    have hb := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n
    have hb' := mul_le_mul_of_nonneg_left hb hg'0.le
    have hb1 := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)
    have hb1' := mul_le_mul_of_nonneg_left hb1 hg'0.le
    have e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n := by
      linear_combination (n : ℝ) * hg'1
    have e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1) := by
      push_cast; linear_combination ((n : ℝ) + 1) * hg'1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre' := hre e
    rw [hr a]
    split_ifs with hga
    · have hL' := hLg hga
      have e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n := by
        rw [_root_.pow_succ, ← hgp]; ring
      rw [e3]; linarith
    · have e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1) := by ring
      rw [e4]; linarith
  have step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a) := by
    intro D
    induction D with
    | zero => intro a α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum p c t e) = coeff α (z e) := by rw [hlg e]
      have h2 : coeff α (lgSum p c t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n)) :=
        rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e) := by
        simp [h0, Pi.single_apply]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub (hz e α) ?_
      refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
      have hN : 2 ≤ p ^ (n + 1) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h4 := (ih a).pow (ht a) hN α hα
      rw [v.map_mul]
      by_cases hga : good a
      · have hc1 := hgood a hga (n + 1) e (by omega)
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith)
          (by push_cast; linarith)
        push_cast at this ⊢
        linarith
      · have hc1 := hc a (n + 1) e
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)
        push_cast at this ⊢
        linarith
  intro b α
  exact step (Finsupp.degree α + 1) b α (by omega)

/- English proof (translation)
Introduce `C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg`. Conclude with `ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl) hz ht hlg`.
-/
theorem ordGe_of_lgSum_twoRadii :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  intro C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg
  exact ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t
    (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl)
    hz ht hlg

end GlobalTheory.ExpWeightTwoRadii
