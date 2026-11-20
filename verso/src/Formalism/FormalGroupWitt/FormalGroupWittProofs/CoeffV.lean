import Formalism.FormalGroupWitt.SubstInjectiveV

noncomputable section

universe u v w

namespace Formalism.FG.CoefficientBoundsFormalGroupWitt

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Unfold `IsFrobLift at hσ`. Establish `h1` using `hσ a ha`. Establish `h2 : ‖a ^ q‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) ha`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  unfold IsFrobLift at hσ
  have h1 := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp) h2

/- English proof (translation)
Simplify using `only [map_sub, map_smul, map_sum, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma coeff_split {ι : Type v} [Fintype ι] {τ : Type w} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) (f : ι → MvPowerSeries τ K) (j : ι) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n (f j) = MvPowerSeries.coeff n (f j - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) +
      (p : K)⁻¹ * ∑ k, M j k *
        MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) := by
  simp only [map_sub, map_smul, map_sum, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `Formalism.FG.CoeffBoundV`. Introduce `K _ _ _ p q hq σ hS ι _ M hM τ f h0 hF`. Unfold `FunctionalEquationSetting at hS`. Unfold `IntegralMat at hM`. Unfold `IsFunEqTypeV at hF`.

Take `⟨hpp, ⟨h, hh, hqe⟩, hp1, hσ⟩` from `hS`. Establish `hq1 : 1 < q`. Rewrite using `[hqe]`. Conclude with `Nat.one_lt_pow hh.ne' hpp.one_lt`. Establish `hP0 : 0 < ‖(p : K)‖`.

Rewrite using `[norm_pos_iff]`. Conclude with `hpp.ne_zero` after adjusting the coercions. Establish `hg : ∀ j n, ‖MvPowerSeries.coeff n (f j - (p : K)⁻¹ • ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k)))‖ ≤ 1`. Introduce `j n`. Establish `h3` using `hF j`.

Unfold `IntegralMv at h3`. Conclude with `h3 n`. Establish `hσn : ∀ (x : K) (e : ℕ), ‖x‖ * ‖(p : K)‖ ^ e ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ e ≤ 1`. Introduce `x e hx`. Establish `h4 : ‖(p : K) ^ e * x‖ ≤ 1`.

Rewrite using `[norm_mul, norm_pow, mul_comm]`. Conclude with `hx`. Establish `h5` using `sigma_norm_le_one hp1.le hσ _ h4`. Rewrite `h5` using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow, mul_comm]`. Conclude with `h5`.

Establish `key : ∀ d : ℕ, ∀ n : τ →₀ ℕ, Finsupp.degree n = d → ∀ j, ∃ k, (∀ i, q ^ k ∣ n i) ∧ ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `n hn j`.

Establish `hc` using `coeff_split p q hq σ M f j n`. Distinguish the cases in `hdiv : ∀ i, q ∣ n i`. Distinguish the cases in `hn0 : n = 0`. Use `⟨0, fun i => by simp, ?_⟩` and prove the remaining obligations. Substitute `hn0` using the available equality.

Establish `h6` using `h0 j`. Rewrite `h6` using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[h6]`. Simplify using the standard rewrite rules. Take `⟨m, hm⟩ : ∃ m : τ →₀ ℕ, n = q • m` from `⟨Finsupp.mapRange (fun e => e / q) (Nat.zero_div q) n, by`.

Use extensionality with `i`. Simplify using `[Nat.mul_div_cancel' (hdiv i)]⟩`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Apply `hn0` to reduce the goal to its premises.

Rewrite using `[hm, smul_zero]`. Establish `hlt : Finsupp.degree m < d`. Rewrite using `[← hn, hm, map_nsmul, smul_eq_mul]`. Establish `h7 : Finsupp.degree m ≠ 0` using `fun h8 => hm0 ((Finsupp.degree_eq_zero_iff m).mp h8)`. Establish `h9 : 0 < Finsupp.degree m` using `Nat.pos_of_ne_zero h7`.

Use the polynomial consequences of the given equalities and inequalities. Use `choose kk hkk using fun l => ih _ hlt m rfl l`. Take `⟨l0, -, hl0⟩` from `Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ _⟩ kk`. Use `set K0 := Finset.univ.sup kk with hK0`. Establish `hK : ∀ i, q ^ K0 ∣ m i`.

Rewrite using `[hl0]`. Conclude with `(hkk l0).1`. Establish `hb : ∀ l, ‖MvPowerSeries.coeff m (f l)‖ * ‖(p : K)‖ ^ K0 ≤ 1`. Introduce `l`. Establish `h10 : ‖(p : K)‖ ^ K0 ≤ ‖(p : K)‖ ^ kk l` using `pow_le_pow_of_le_one hP0.le hp1.le (Finset.le_sup (Finset.mem_univ l))`.

Conclude with `(mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans (hkk l).2`. Establish `hterm : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) = σ (MvPowerSeries.coeff m (f l))`. Introduce `l`. Rewrite using `[hm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map]`. Establish `hPK : 0 < ‖(p : K)‖ ^ K0` using `pow_pos hP0 K0`.

Establish `hS : ‖∑ l, M j l * MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ ≤ 1 / ‖(p : K)‖ ^ K0`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[hterm, norm_mul, le_div_iff₀ hPK]`. Establish `h11` using `hσn _ _ (hb l)`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨K0 + 1, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, Finsupp.smul_apply, smul_eq_mul, pow_succ, mul_comm (q ^ K0)]`. Conclude with `mul_dvd_mul_left q (hK i)`. Rewrite using `[hc]`.

Use `(mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)).trans ?_` and prove the remaining obligations. Rewrite using `[max_mul_of_nonneg _ _ (by positivity)]`. Apply `max_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_inv, pow_succ]`.

Establish `h12` using `(le_div_iff₀ hPK).mp hS`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ 1 := h12`. Use `push_neg at hdiv`.

Take `⟨i, hi⟩` from `hdiv`. Use `⟨0, fun i => by simp, ?_⟩` and prove the remaining obligations. Establish `hz : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) = 0` using `fun l => MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi`. Rewrite using `[hc]`. Simplify using `only [hz, mul_zero, Finset.sum_const_zero, add_zero, pow_zero, mul_one]`.

Conclude with `hg j n`. Introduce `j n`. Conclude with `key _ n rfl j`.
-/
theorem main : Formalism.FG.CoeffBoundV.{u, v, w} := by
  unfold Formalism.FG.CoeffBoundV
  intro K _ _ _ p q hq σ hS ι _ M hM τ f h0 hF
  unfold FunctionalEquationSetting at hS
  unfold IntegralMat at hM
  unfold IsFunEqTypeV at hF
  obtain ⟨hpp, ⟨h, hh, hqe⟩, hp1, hσ⟩ := hS
  have hq1 : 1 < q := by
    rw [hqe]
    exact Nat.one_lt_pow hh.ne' hpp.one_lt
  have hP0 : 0 < ‖(p : K)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hpp.ne_zero
  have hg : ∀ j n, ‖MvPowerSeries.coeff n (f j - (p : K)⁻¹ •
      ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k)))‖ ≤ 1 := by
    intro j n
    have h3 := hF j
    unfold IntegralMv at h3
    exact h3 n
  have hσn : ∀ (x : K) (e : ℕ), ‖x‖ * ‖(p : K)‖ ^ e ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ e ≤ 1 := by
    intro x e hx
    have h4 : ‖(p : K) ^ e * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow, mul_comm]
      exact hx
    have h5 := sigma_norm_le_one hp1.le hσ _ h4
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, mul_comm] at h5
    exact h5
  have key : ∀ d : ℕ, ∀ n : τ →₀ ℕ, Finsupp.degree n = d → ∀ j, ∃ k, (∀ i, q ^ k ∣ n i) ∧
      ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro n hn j
    have hc := coeff_split p q hq σ M f j n
    by_cases hdiv : ∀ i, q ∣ n i
    · by_cases hn0 : n = 0
      · refine ⟨0, fun i => by simp, ?_⟩
        subst hn0
        have h6 := h0 j
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h6
        rw [h6]
        simp
      · obtain ⟨m, hm⟩ : ∃ m : τ →₀ ℕ, n = q • m :=
          ⟨Finsupp.mapRange (fun e => e / q) (Nat.zero_div q) n, by
            ext i
            simp [Nat.mul_div_cancel' (hdiv i)]⟩
        have hm0 : m ≠ 0 := by
          rintro rfl
          apply hn0
          rw [hm, smul_zero]
        have hlt : Finsupp.degree m < d := by
          rw [← hn, hm, map_nsmul, smul_eq_mul]
          have h7 : Finsupp.degree m ≠ 0 := fun h8 => hm0 ((Finsupp.degree_eq_zero_iff m).mp h8)
          have h9 : 0 < Finsupp.degree m := Nat.pos_of_ne_zero h7
          nlinarith
        choose kk hkk using fun l => ih _ hlt m rfl l
        obtain ⟨l0, -, hl0⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ _⟩ kk
        set K0 := Finset.univ.sup kk with hK0
        have hK : ∀ i, q ^ K0 ∣ m i := by
          rw [hl0]
          exact (hkk l0).1
        have hb : ∀ l, ‖MvPowerSeries.coeff m (f l)‖ * ‖(p : K)‖ ^ K0 ≤ 1 := by
          intro l
          have h10 : ‖(p : K)‖ ^ K0 ≤ ‖(p : K)‖ ^ kk l :=
            pow_le_pow_of_le_one hP0.le hp1.le (Finset.le_sup (Finset.mem_univ l))
          exact (mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans (hkk l).2
        have hterm : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) =
            σ (MvPowerSeries.coeff m (f l)) := by
          intro l
          rw [hm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map]
        have hPK : 0 < ‖(p : K)‖ ^ K0 := pow_pos hP0 K0
        have hS : ‖∑ l, M j l * MvPowerSeries.coeff n
            (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ ≤ 1 / ‖(p : K)‖ ^ K0 := by
          apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
          intro l _
          rw [hterm, norm_mul, le_div_iff₀ hPK]
          have h11 := hσn _ _ (hb l)
          calc ‖M j l‖ * ‖σ (MvPowerSeries.coeff m (f l))‖ * ‖(p : K)‖ ^ K0
              ≤ 1 * ‖σ (MvPowerSeries.coeff m (f l))‖ * ‖(p : K)‖ ^ K0 := by gcongr; exact hM j l
            _ ≤ 1 := by rw [one_mul]; exact h11
        refine ⟨K0 + 1, fun i => ?_, ?_⟩
        · rw [hm, Finsupp.smul_apply, smul_eq_mul, pow_succ, mul_comm (q ^ K0)]
          exact mul_dvd_mul_left q (hK i)
        · rw [hc]
          refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
            (by positivity)).trans ?_
          rw [max_mul_of_nonneg _ _ (by positivity)]
          apply max_le
          · calc _ ≤ 1 * 1 := mul_le_mul (hg j n) (pow_le_one₀ hP0.le hp1.le) (by positivity) zero_le_one
              _ = 1 := one_mul 1
          · rw [norm_mul, norm_inv, pow_succ]
            have h12 := (le_div_iff₀ hPK).mp hS
            calc ‖(p : K)‖⁻¹ * ‖∑ l, M j l * MvPowerSeries.coeff n
                  (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ * (‖(p : K)‖ ^ K0 * ‖(p : K)‖)
                = ‖∑ l, M j l * MvPowerSeries.coeff n
                  (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ * ‖(p : K)‖ ^ K0 := by
                  field_simp
              _ ≤ 1 := h12
    · push_neg at hdiv
      obtain ⟨i, hi⟩ := hdiv
      refine ⟨0, fun i => by simp, ?_⟩
      have hz : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) = 0 :=
        fun l => MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi
      rw [hc]
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero, pow_zero, mul_one]
      exact hg j n
  intro j n
  exact key _ n rfl j

end Formalism.FG.CoefficientBoundsFormalGroupWitt

/- English proof (translation)
The claim follows from `Formalism.FG.CoefficientBoundsFormalGroupWitt.main.{u, v, w}`.
-/
theorem Formalism.FG.coeff_bound_vector : Formalism.FG.CoeffBoundV.{u, v, w} := Formalism.FG.CoefficientBoundsFormalGroupWitt.main.{u, v, w}
