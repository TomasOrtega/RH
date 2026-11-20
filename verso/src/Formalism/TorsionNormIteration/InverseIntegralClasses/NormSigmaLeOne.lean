import Formalism.TorsionNormIteration.InvIntegralOfClass

noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT

open Formalism.G

namespace InverseIntegralClassesKeyFacts

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Distinguish the cases in `hfin : (Function.support g).Finite`. Rewrite using `[finsum_eq_sum g hfin]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)`. Rewrite using `[finsum_of_infinite_support hfin]`. Simplify using `using hC`.
-/
lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`.
-/
lemma norm_add_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)`.
-/
lemma norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)

/- English proof (translation)
Establish `h1 : ‖σ a - a ^ q‖ ≤ 1` using `(hσ a ha).trans hp1`. Establish `h2 : ‖a ^ q‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha`. Establish `: σ a = (σ a - a ^ q) + a ^ q` using `by ring`. Rewrite using `[this]`. Conclude with `norm_add_le_of h1 h2`.
-/
lemma norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ 1 := (hσ a ha).trans hp1
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]; exact norm_add_le_of h1 h2

end InverseIntegralClassesKeyFacts

open InverseIntegralClassesKeyFacts

/- English proof (translation)
Introduce `K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI`. Take `⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩` from `id hS`. Establish `hp1' : ‖(p : K)‖ ≤ 1` using `hp1.le`. Establish `hpne : (p : K) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hppos : 0 < ‖(p : K)‖` using `norm_pos_iff.mpr hpne`.

Use `set fs : PowerSeries K := PowerSeries.map σ f with hfs`. Use `set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg`. Use `set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ`. Establish `hαS : PowerSeries.HasSubst α` using `HasSubst.of_constantCoeff_zero hα0`. Establish `hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0`.

Rewrite using `[map_pow, hα0, zero_pow hq]`. Establish `hαqS : PowerSeries.HasSubst (α ^ q)` using `HasSubst.of_constantCoeff_zero hαq0`. Establish `hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0`. Simplify using `[hα0]`. Establish `hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α)` using `HasSubst.of_constantCoeff_zero hmα0`.

Establish `hβ0 : MvPowerSeries.constantCoeff β = 0`. Rewrite using `[hβ, MvPowerSeries.constantCoeff_expand, hmα0]`. Establish `hβS : PowerSeries.HasSubst β` using `HasSubst.of_constantCoeff_zero hβ0`. Establish `hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q)` using `HasSubst.of_constantCoeff_zero' (by simp [hq])`. Establish `hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β)`.

Establish `e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q)`. Rewrite using `[hg]`. Normalize the expressions using the abelian group laws. Establish `e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q)`. Rewrite using `[PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS]`.

Establish `e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β`. Rewrite using `[PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]`. Establish `e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q)` using `by conv_lhs => rw [e1]`. Rewrite using `[PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]`. Rewrite using `[e3, e4, smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q)`. Introduce `n`. Rewrite using `[PowerSeries.coeff_X_pow]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hαqI : IntegralMv (α ^ q)`. Use `h4 K ι _ α hXqI hα0 hαI` as an intermediate fact. Rewrite `this` using `[PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS]`. Then use the resulting hypothesis. Establish `hdiv : DivByMv (p : K) (α ^ q - β)` using `h7 K p q hq σ hS ι α hαI`. Establish `hβI : IntegralMv β`.

Introduce `d`. Establish `e : MvPowerSeries.coeff d β = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')`. Establish `hgI : IntegralMv (g.subst α)` using `h4 K ι g α hfT hα0 hαI`. Establish `hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖`. Introduce `d`. Rewrite using `[map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS, ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d) (PowerSeries.coeff_subst_finite hβS fs d)]`.

Apply `norm_finsum_le (norm_nonneg _)` to reduce the goal to its premises. Introduce `n`. Rewrite using `[← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]`. Take `⟨k, hkdvd, hk⟩` from `h5 K p q σ hS f hf0 hfT n`. Take `⟨m, rfl⟩` from `hkdvd`.

Establish `hn : q ^ k * m = p ^ (h * k) * m` using `by rw [hqh, ← pow_mul]`. Establish `hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β)` using `by simpa using hdiv`. Establish `hc0` using `h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d`. Rewrite `hc0` using `[← hn]`. Establish `hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1`.

Establish `h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1` using `by rw [norm_mul, norm_pow]; exact hk`. Establish `h'` using `norm_sigma_le_one hσ hp1' h0`. Rewrite `h'` using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow]`. Then use the resulting hypothesis. Establish `hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖ ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖`. Use `hc0.trans ?_` and prove the remaining obligations.

Rewrite using `[norm_pow, pow_add, pow_one, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Unfold `IsFunEqTypeMv`. Rewrite using `[hdec]`.

Introduce `d`. Rewrite using `[map_add, MvPowerSeries.coeff_smul]`. Use `norm_add_le_of (hgI d) ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne

  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : PowerSeries.HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : PowerSeries.HasSubst (α ^ q) := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α) := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : MvPowerSeries.constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : PowerSeries.HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q) :=
    HasSubst.of_constantCoeff_zero' (by simp [hq])

  have hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α))
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]; abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS,
        PowerSeries.subst_X hαS]
    have e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]; abel

  have hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q) := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv (α ^ q) := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS] at this
  have hdiv : DivByMv (p : K) (α ^ q - β) := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : MvPowerSeries.coeff d β
        = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')
  have hgI : IntegralMv (g.subst α) := h4 K ι g α hfT hα0 hαI

  have hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS,
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d)
        (PowerSeries.coeff_subst_finite hβS fs d)]
    apply norm_finsum_le (norm_nonneg _)
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β) := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add, MvPowerSeries.coeff_smul]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'

end Formalism.LT
