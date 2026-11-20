import Mathlib

noncomputable def UpperTheory.Reformulated.B.Gwb7.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwb7.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.Gwb7.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

/- English proof (translation)
Introduce `p _ σ F i hF n`. Establish `h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1` using `hF _`. Establish `h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1`. Establish `h` using `IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)`. Rewrite `h` using `[Nat.cast_add, Nat.cast_one]`. Then use the resulting hypothesis.

Express the relevant statement in the definitionally equal form `‖MvPowerSeries.coeff n (MvPowerSeries.pderiv ℂ_[p] i F)‖ ≤ 1`. Rewrite using `[MvPowerSeries.coeff_pderiv, norm_mul]`. Conclude with `mul_le_one₀ h1 (norm_nonneg _) h2`.
-/
theorem UpperTheory.Reformulated.B.Gwb7.intMv_pderiv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv ℂ_[p] i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by
  intro p _ σ F i hF n
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)
    rwa [Nat.cast_add, Nat.cast_one] at h
  change ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv ℂ_[p] i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2
