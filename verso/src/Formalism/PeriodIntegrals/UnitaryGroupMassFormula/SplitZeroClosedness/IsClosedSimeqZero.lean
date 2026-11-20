import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.ZcFacts

noncomputable section

open Classical

namespace PI.SZGW

open PI.BeDiagZp.ContPf

/- English proof (translation)
Establish `hF : CC fun c => G c - 0` using `cc_sub hG (cc_const 0)`. Establish `hE` using `cc_expMv hF`. Simplify using `only [PI.BeDiagZp.Simeq, PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_and, Set.ofPred_forall]`. Use `IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)` and prove the remaining obligations. Conclude with `(hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _`.
-/
theorem isClosed_simeq_zero {p : ℕ} [Fact p.Prime] {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (hG : CC G) : IsClosed {c : ℂ_[p] | PI.BeDiagZp.Simeq (G c) 0} := by
  have hF : CC fun c => G c - 0 := cc_sub hG (cc_const 0)
  have hE := cc_expMv hF
  simp only [PI.BeDiagZp.Simeq, PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_and,
    Set.ofPred_forall]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const)
    (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
  exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _

/- English proof (translation)
Simplify using `only [PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_forall]`. Conclude with `isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hG α)) continuous_const`.
-/
theorem isClosed_int {p : ℕ} [Fact p.Prime] {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (hG : CC G) : IsClosed {c : ℂ_[p] | PI.BeDiagZp.IntegralMv (G c)} := by
  simp only [PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_forall]
  exact isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hG α)) continuous_const

/- English proof (translation)
Introduce `p _ σ G hG hN c`. Establish `hcl'` using `(isClosed_simeq_zero hG).preimage zc_continuous`. Use `PadicInt.denseRange_natCast.induction_on c hcl' ?_` and prove the remaining obligations. Introduce `k`. Use `show PI.BeDiagZp.Simeq _ _`.

Rewrite using `[zc_natCast]`. Conclude with `hN k`.
-/
theorem zpSimeq_holds : ZpSimeq := by
  intro p _ σ G hG hN c
  have hcl' := (isClosed_simeq_zero hG).preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on c hcl' ?_
  intro k
  show PI.BeDiagZp.Simeq _ _
  rw [zc_natCast]
  exact hN k

/- English proof (translation)
Introduce `p _ σ G hG hN c`. Establish `hcl'` using `(isClosed_int hG).preimage zc_continuous`. Use `PadicInt.denseRange_natCast.induction_on c hcl' ?_` and prove the remaining obligations. Introduce `k`. Use `show PI.BeDiagZp.IntegralMv _`.

Rewrite using `[zc_natCast]`. Conclude with `hN k`.
-/
theorem zpInt_holds : ZpInt := by
  intro p _ σ G hG hN c
  have hcl' := (isClosed_int hG).preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on c hcl' ?_
  intro k
  show PI.BeDiagZp.IntegralMv _
  rw [zc_natCast]
  exact hN k

/- English proof (translation)
Rewrite using `[PadicInt.isUnit_iff]`. Use `le_antisymm (PadicInt.norm_le_one _) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `e : (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p])` using `by norm_cast`.

Rewrite `hlt` using `[e, PadicInt.norm_int_lt_one_iff_dvd]`. Establish `hd : p ∣ 2` using `by exact_mod_cast hlt`. Establish `hle` using `Nat.le_of_dvd (by norm_num) hd`. Establish `hge` using `hp.out.two_le`. Use linear arithmetic over natural numbers and integers.
-/
theorem isUnit_two {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  rw [not_le] at hlt
  have e : (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) := by norm_cast
  rw [e, PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have hd : p ∣ 2 := by exact_mod_cast hlt
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hge := hp.out.two_le
  omega

/- English proof (translation)
Introduce `p _ h2`. Use `⟨?_, ?_, ?_, ?_, ?_, isUnit_two h2⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `[PI.BeDiagZp.zc]`. Introduce `a b`.

Simplify using `[PI.BeDiagZp.zc]`. Simplify using `[PI.BeDiagZp.zc]`. Simplify using `[PI.BeDiagZp.zc]`. Simplify using `only [PI.BeDiagZp.zc]`. Establish `e : ((2 : ℤ_[p]) : ℚ_[p]) = 2` using `by norm_cast`.

Rewrite using `[e, map_ofNat]`.
-/
theorem zcFacts_holds : ZcFacts := by
  intro p _ h2
  refine ⟨?_, ?_, ?_, ?_, ?_, isUnit_two h2⟩
  · intro a b; simp [PI.BeDiagZp.zc]
  · intro a b; simp [PI.BeDiagZp.zc]
  · simp [PI.BeDiagZp.zc]
  · simp [PI.BeDiagZp.zc]
  · simp only [PI.BeDiagZp.zc]
    have e : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by norm_cast
    rw [e, map_ofNat]

end PI.SZGW
