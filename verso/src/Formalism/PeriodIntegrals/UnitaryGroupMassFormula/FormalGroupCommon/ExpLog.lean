import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum

noncomputable section

namespace PI.FglShared

open MvPowerSeries

section Field

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Rewrite using `[PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha), finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Simplify using `[ha, hd]`.
-/
theorem constantCoeff_subst_of_zero {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f : PowerSeries K) : constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [ha, hd]

/- English proof (translation)
Establish `hu : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries K) ≠ 0` using `by simp`. Establish `hinv` using `PowerSeries.inv_mul_cancel _ hu`. Establish `hD : PowerSeries.derivative K (g * (1 + PowerSeries.X)⁻¹) = PowerSeries.derivative K 1`. Simplify using `only [Derivation.leibniz, PowerSeries.derivative_inv', hd, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul, zero_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc : PowerSeries.constantCoeff (g * (1 + PowerSeries.X)⁻¹) = PowerSeries.constantCoeff (1 : PowerSeries K)`. Simplify using `[PowerSeries.constantCoeff_inv, h0]`. Establish `h1` using `PowerSeries.derivative.ext hD hc`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_one_add_X_of_deriv {g : PowerSeries K}
    (hd : PowerSeries.derivative K g = g * (1 + PowerSeries.X)⁻¹)
    (h0 : PowerSeries.constantCoeff g = 1) : g = 1 + PowerSeries.X := by
  have hu : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries K) ≠ 0 := by simp
  have hinv := PowerSeries.inv_mul_cancel _ hu
  have hD : PowerSeries.derivative K (g * (1 + PowerSeries.X)⁻¹) = PowerSeries.derivative K 1 := by
    simp only [Derivation.leibniz, PowerSeries.derivative_inv', hd, map_add,
      Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul, zero_add]
    ring
  have hc : PowerSeries.constantCoeff (g * (1 + PowerSeries.X)⁻¹) =
      PowerSeries.constantCoeff (1 : PowerSeries K) := by
    simp [PowerSeries.constantCoeff_inv, h0]
  have h1 := PowerSeries.derivative.ext hD hc
  calc g = g * ((1 + PowerSeries.X)⁻¹ * (1 + PowerSeries.X)) := by rw [hinv, mul_one]
    _ = (g * (1 + PowerSeries.X)⁻¹) * (1 + PowerSeries.X) := by ring
    _ = 1 + PowerSeries.X := by rw [h1, one_mul]

/- English proof (translation)
Rewrite using `[PowerSeries.deriv_log, PowerSeries.eq_inv_iff_mul_eq_one (by simp)]`. Use extensionality with `n`. Break down `n with _ | n` into its components or cases. Rewrite using `[mul_add, mul_one, map_add, PowerSeries.coeff_zero_mul_X, add_zero, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_pos rfl]`. Simplify using the standard rewrite rules.

Rewrite using `[mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ← map_add]`. Simplify using `[pow_succ]`.
-/
theorem derivative_log_eq : PowerSeries.derivative K (PowerSeries.log K) = (1 + PowerSeries.X)⁻¹ := by
  rw [PowerSeries.deriv_log, PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rcases n with _ | n
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_zero_mul_X, add_zero, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_pos rfl]
    simp
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ← map_add]
    simp [pow_succ]

/- English proof (translation)
Apply `eq_one_add_X_of_deriv` to reduce the goal to its premises. Rewrite using `[PowerSeries.derivative_subst PowerSeries.HasSubst.log, PowerSeries.derivative_exp, derivative_log_eq]`. Establish `h` using `constantCoeff_subst_of_zero (τ := Unit) (a := PowerSeries.log K) PowerSeries.constantCoeff_log (PowerSeries.exp K)`. Rewrite `h` using `[PowerSeries.constantCoeff_exp]`. Conclude with `h`.
-/
theorem exp_subst_log :
    PowerSeries.subst (PowerSeries.log K) (PowerSeries.exp K) = (1 + PowerSeries.X : PowerSeries K) := by
  apply eq_one_add_X_of_deriv
  · rw [PowerSeries.derivative_subst PowerSeries.HasSubst.log, PowerSeries.derivative_exp,
      derivative_log_eq]
  · have h := constantCoeff_subst_of_zero (τ := Unit) (a := PowerSeries.log K)
      PowerSeries.constantCoeff_log (PowerSeries.exp K)
    rw [PowerSeries.constantCoeff_exp] at h
    exact h

end Field

section Padic

variable {p : ℕ} [Fact p.Prime]

def logS {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_logS {σ : Type} (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (logS F) = ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
      if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * coeff α ((F - 1) ^ n) / (n : ℂ_[p]) :=
  rfl

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_logS]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_logS {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : constantCoeff (logS F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logS]
  simp

/- English proof (translation)
The claim follows from `PI.FglPhSplit.Wk.expMv_add hf hg`.
-/
theorem expMv_add' {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : PI.FglPhSplit.expMv (f + g) = PI.FglPhSplit.expMv f * PI.FglPhSplit.expMv g :=
  PI.FglPhSplit.Wk.expMv_add hf hg

/- English proof (translation)
Establish `hF' : constantCoeff (F - 1) = 0` using `by simp [hF]`. Establish `ha : PowerSeries.HasSubst (F - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero hF'`. Use extensionality with `α`. Rewrite using `[coeff_logS, PowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[if_neg hn.ne', PowerSeries.coeff_log, if_neg hn.ne', smul_eq_mul]`. Simplify using `only [map_div₀, map_pow, map_neg, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `n hn`. Simplify using `only [Function.mem_support, ne_eq] at hn`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hlt`. Apply `hn` to reduce the goal to its premises.

Establish `hdeg : Finsupp.degree α < n`. Rewrite using `[← PI.FglPhSplit.Wk.deg_eq]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[PI.FglPhSplit.Wk.coeff_pow_eq_zero' hF' hdeg, smul_zero]`.
-/
theorem logS_eq_subst {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 1) :
    logS F = PowerSeries.subst (F - 1) (PowerSeries.log ℂ_[p]) := by
  have hF' : constantCoeff (F - 1) = 0 := by simp [hF]
  have ha : PowerSeries.HasSubst (F - 1) := PowerSeries.HasSubst.of_constantCoeff_zero hF'
  ext α
  rw [coeff_logS, PowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', PowerSeries.coeff_log, if_neg hn.ne', smul_eq_mul]
      simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
      ring
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hn
    have hdeg : Finsupp.degree α < n := by
      rw [← PI.FglPhSplit.Wk.deg_eq]
      omega
    rw [PI.FglPhSplit.Wk.coeff_pow_eq_zero' hF' hdeg, smul_zero]

/- English proof (translation)
Establish `hF' : constantCoeff (F - 1) = 0` using `by simp [hF]`. Establish `ha : PowerSeries.HasSubst (F - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero hF'`. Establish `h1 : PowerSeries.subst (F - 1) (1 : PowerSeries ℂ_[p]) = 1`. Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_one]`. Rewrite using `[PI.FglPhSplit.Wk.expMv_eq_subst (constantCoeff_logS F), logS_eq_subst hF, ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log ha, exp_subst_log, PowerSeries.subst_add ha, PowerSeries.subst_X ha, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expMv_logS {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 1) :
    PI.FglPhSplit.expMv (logS F) = F := by
  have hF' : constantCoeff (F - 1) = 0 := by simp [hF]
  have ha : PowerSeries.HasSubst (F - 1) := PowerSeries.HasSubst.of_constantCoeff_zero hF'
  have h1 : PowerSeries.subst (F - 1) (1 : PowerSeries ℂ_[p]) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PI.FglPhSplit.Wk.expMv_eq_subst (constantCoeff_logS F), logS_eq_subst hF,
    ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log ha, exp_subst_log,
    PowerSeries.subst_add ha, PowerSeries.subst_X ha, h1]
  ring

/- English proof (translation)
Establish `hxs : PowerSeries.HasSubst x` using `PowerSeries.HasSubst.of_constantCoeff_zero hx`. Establish `hfs : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Rewrite using `[PI.FglPhSplit.Wk.expMv_eq_subst (PowerSeries.constantCoeff_subst_eq_zero hx f hf), PI.FglPhSplit.Wk.expMv_eq_subst hf, PowerSeries.subst_comp_subst_apply hfs hxs]`.
-/
theorem expMv_subst' {σ : Type} {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    {f : PowerSeries ℂ_[p]} (hf : MvPowerSeries.constantCoeff f = 0) :
    PI.FglPhSplit.expMv (PowerSeries.subst x f) = PowerSeries.subst x (PI.FglPhSplit.expMv f) := by
  have hxs : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PI.FglPhSplit.Wk.expMv_eq_subst (PowerSeries.constantCoeff_subst_eq_zero hx f hf),
    PI.FglPhSplit.Wk.expMv_eq_subst hf, PowerSeries.subst_comp_subst_apply hfs hxs]

/- English proof (translation)
Establish `hn0' : coeff 0 n = 1` using `by rw [coeff_zero_eq_constantCoeff_apply, hn0]`. It suffices to establish `H : ∀ d : ℕ, ∀ α : σ →₀ ℕ, Finsupp.degree α = d → ‖coeff α u‖ ≤ 1 from fun α => H _ α rfl`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on`. Name the introduced variables `d ih`.

Introduce `α hd`. Establish `hmem : (α, (0 : σ →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal α` using `by simp`. Establish `key : coeff α u + ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n = coeff α (1 : MvPowerSeries σ ℂ_[p])`. Rewrite using `[← h, coeff_mul, ← Finset.add_sum_erase _ _ hmem]`. Simplify using `[hn0', hn0]`.

Establish `hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n‖ ≤ 1`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `x hx`. Take `⟨hne, hx⟩` from `Finset.mem_erase.mp hx`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `h2 : x.2 ≠ 0`. Introduce `h0`. Conclude with `hne (Prod.ext (by simpa [h0] using hx) (by simpa using h0))`. Establish `hdeg : Finsupp.degree x.1 < d`. Establish `hsum` using `congrArg Finsupp.degree hx`.

Rewrite `hsum` using `[map_add]`. Establish `: Finsupp.degree x.2 ≠ 0` using `by rwa [Ne, Finsupp.degree_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (ih _ hdeg x.1 rfl) (norm_nonneg _) (hn _)`.

Rewrite using `[eq_sub_of_add_eq key, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rw [coeff_one] split_ifs <;> simp`. Rewrite using `[norm_neg]` and apply the resulting hypothesis.
-/
theorem int_of_mul_eq_one {σ : Type} [DecidableEq σ] {u n : MvPowerSeries σ ℂ_[p]}
    (hn : ∀ α, ‖coeff α n‖ ≤ 1) (hn0 : constantCoeff n = 1) (h : u * n = 1) :
    ∀ α, ‖coeff α u‖ ≤ 1 := by
  have hn0' : coeff 0 n = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hn0]
  suffices H : ∀ d : ℕ, ∀ α : σ →₀ ℕ, Finsupp.degree α = d → ‖coeff α u‖ ≤ 1 from
    fun α => H _ α rfl
  intro d
  induction d using Nat.strong_induction_on
  rename_i d ih
  intro α hd
  have hmem : (α, (0 : σ →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal α := by simp
  have key : coeff α u + ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n =
      coeff α (1 : MvPowerSeries σ ℂ_[p]) := by
    rw [← h, coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    simp [hn0', hn0]
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro x hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h2 : x.2 ≠ 0 := by
      intro h0
      exact hne (Prod.ext (by simpa [h0] using hx) (by simpa using h0))
    have hdeg : Finsupp.degree x.1 < d := by
      have hsum := congrArg Finsupp.degree hx
      rw [map_add] at hsum
      have : Finsupp.degree x.2 ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
      omega
    rw [norm_mul]
    exact mul_le_one₀ (ih _ hdeg x.1 rfl) (norm_nonneg _) (hn _)
  rw [eq_sub_of_add_eq key, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_one]
    split_ifs <;> simp
  · rwa [norm_neg]

end Padic

end PI.FglShared

end
