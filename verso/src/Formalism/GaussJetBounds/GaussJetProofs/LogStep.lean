import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `h` using `sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk`. Establish `hl2` using `hl.two_le`. Establish `h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1` using `by omega`. Establish `h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ)`.

Conclude with `h1` after adjusting the coercions. Rewrite `h2` using `[Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk), Nat.cast_one]`. Establish `hpos : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast hl2`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[mul_one_div, le_div_iff₀ hpos, mul_comm]`. Conclude with `h2`.
-/
theorem padicValNat_factorial_le_sub_one_div {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : k ≠ 0) :
    (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) * (1 / ((l : ℝ) - 1)) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk
  have hl2 := hl.two_le
  have h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1 := by omega
  have h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk),
    Nat.cast_one] at h2
  have hpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
    linarith
  rw [mul_one_div, le_div_iff₀ hpos, mul_comm]
  exact h2

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div, Formalism.LT.ExpP.norm_natCast_eq hl hπ (Nat.factorial_ne_zero k)]`.
-/
theorem norm_coeff_exp {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hπ : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div,
    Formalism.LT.ExpP.norm_natCast_eq hl hπ (Nat.factorial_ne_zero k)]

/- English proof (translation)
Introduce `K _ _ _ l hl hπ ι r D hD0 hE`. Establish `hπ0 : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)`. Establish `hπ1 : ‖(l : K)‖ ≤ 1` using `hπ.le`. Establish `hD1 : Low 1 D` using `(low_one_iff _).2 hD0`. Establish `hs : PowerSeries.HasSubst D` using `PowerSeries.HasSubst.of_constantCoeff_zero hD0`.

It suffices to establish `H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N → MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `n hn`.

Distinguish the cases in `hn0 : n = 0`. Substitute `hn0` using the available equality. Rewrite using `[monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]`. Conclude with `Real.rpow_nonneg hπ0.le _`. Establish `hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D)`.

Introduce `m`. Rewrite using `[monoWtGe_iff, coeff_truncBelow]`. Use `split_ifs with hm`. Conclude with `ih _ hm m rfl`. Simplify using `using Real.rpow_nonneg hπ0.le _`.

Establish `hlow : Low N (D - truncBelow N D)`. Introduce `m hm`. Rewrite using `[map_sub, coeff_truncBelow, if_pos hm, sub_self]`. Establish `hT1 : Low 1 (truncBelow N D)`. Introduce `m hm`.

Rewrite using `[coeff_truncBelow]`. Use `split_ifs`. Conclude with `hD1 m hm`. Both sides reduce to the same expression. Establish `hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1))`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hlow`. Consider the case `succ k ihk`. Establish `e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) = (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D + truncBelow N D ^ (k + 1) * (D - truncBelow N D)` using `by ring`.

Rewrite using `[e]`. Conclude with `low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1)) (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))`. Use `set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha`. Establish `hafin : (Function.support a).Finite` using `PowerSeries.coeff_subst_finite hs _ n`. Use `set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb`.

Use `set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc`. Establish `hbfin : (Function.support b).Finite` using `hafin.subset fun k hk => by`. Simplify using `only [Function.mem_support, hb] at hk ⊢`. Use `split_ifs at hk with h`. Conclude with `absurd rfl hk`.

Conclude with `hk`. Establish `hcfin : (Function.support c).Finite` using `(Set.finite_singleton 1).subset fun k hk => by`. Simplify using `only [Function.mem_support, hc] at hk`. Use `split_ifs at hk with h`. Conclude with `h`.

Conclude with `absurd rfl hk`. Establish `habc : a = fun k => b k + c k`. Use function extensionality and compare the values at `k`. Simplify using `only [hb, hc]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `ha1 : a 1 = coeff n D`. Simplify using `[ha, PowerSeries.coeff_exp]`.

Establish `hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D`. Unfold `mvExp`. Rewrite using `[PowerSeries.coeff_subst hs]`. Express the relevant statement in the definitionally equal form `∑ᶠ k, a k = _`. Rewrite using `[habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]`.

Simplify using `only [hc, if_pos rfl, ha1]`. Establish `hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k)`. Rewrite using `[map_sub, coeff_one, if_neg hn0, sub_zero, hsum]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[monoWtGe_iff, hEq]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Use `norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_` and prove the remaining obligations. Simplify using `only [hb]`. Use `split_ifs with hk1`.

Simplify using `using Real.rpow_nonneg hπ0.le _`. Break down `Nat.lt_or_ge k 2 with hk2 | hk2` into its components or cases. Establish `hk0 : k = 0` using `by omega`. Substitute `hk0` using the available equality. Simplify using `only [ha, pow_zero, coeff_one, if_neg hn0, smul_zero, norm_zero]`.

Conclude with `Real.rpow_nonneg hπ0.le _`. Establish `hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k)`. Use `hpow (k - 1) n (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero]`. Conclude with `this`.

Establish `hbd` using `wtGe_pow hπ0 hTw k n`. Rewrite `hbd` using `[monoWtGe_iff]`. Establish `hv` using `padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)`. Simplify using `only [ha]`. Rewrite using `[smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]`.

Use `set v := padicValNat l k.factorial`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by`.

Apply `Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logarithm_weight_induction : LogStep.{u, v} := by
  intro K _ _ _ l hl hπ ι r D hD0 hE
  classical
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hD1 : Low 1 D := (low_one_iff _).2 hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hπ0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    rw [monoWtGe_iff, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : Low N (D - truncBelow N D) := by
    intro m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := by
    intro m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))

  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h
    · subst h; simp
    · simp
  have ha1 : a 1 = coeff n D := by
    simp [ha, PowerSeries.coeff_exp]
  have hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]
    simp only [hc, if_pos rfl, ha1]
  have hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, coeff_one, if_neg hn0, sub_zero, hsum]
    ring
  rw [monoWtGe_iff, hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · simpa using Real.rpow_nonneg hπ0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, coeff_one, if_neg hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hπ0.le _

  have hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hπ0 hTw k n
  rw [monoWtGe_iff] at hbd
  have hv := padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 (pow_nonneg hπ0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
        nlinarith

end Formalism.DworkPowerSeriesWeights
