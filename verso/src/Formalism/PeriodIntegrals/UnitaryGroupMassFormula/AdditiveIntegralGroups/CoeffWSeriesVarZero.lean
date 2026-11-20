import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using `[wser, PowerSeries.coeff_X_pow_mul']`.
-/
theorem lamA_coeff_wser (wq : PowerSeries ℂ_[p]) (n : ℕ) :
    PowerSeries.coeff n (wser wq) = if 3 ≤ n then PowerSeries.coeff (n - 3) wq else 0 := by
  simp [wser, PowerSeries.coeff_X_pow_mul']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lamA_coeff_lam (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam wq) = PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Apply the tactic sequence `intro h; ext j; fin_cases j <;> simp [h]`.
-/
theorem lamA_single0 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Apply the tactic sequence `intro h; ext j; fin_cases j <;> simp [h]`.
-/
theorem lamA_single1 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

/- English proof (translation)
Rewrite using `[wv, Xv, PowerSeries.coeff_subst_single]`. Conclude with `if_congr (lamA_single0 e) rfl rfl`.
-/
theorem coeff_wSeriesVar_zero (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 0) = if e 1 = 0 then PowerSeries.coeff (e 0) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single0 e) rfl rfl

/- English proof (translation)
Rewrite using `[wv, Xv, PowerSeries.coeff_subst_single]`. Conclude with `if_congr (lamA_single1 e) rfl rfl`.
-/
theorem coeff_wSeriesVar_one (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 1) = if e 0 = 0 then PowerSeries.coeff (e 1) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single1 e) rfl rfl

/- English proof (translation)
Rewrite using `[Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]`. Use `congr 1`. Simplify using `[Finsupp.single_le_iff]`.
-/
theorem lamA_coeff_mul_X (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by
  rw [Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X, coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]`. Establish `a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0` using `by simp`. Establish `a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1` using `by simp`. Establish `a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1` using `by simp`.

Establish `a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1` using `by simp`. Rewrite using `[a1, a2, a3, a4]`. Apply the tactic sequence `by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0`. Simplify using `[h0, h1]`. Establish `: 1 ≤ e 1` using `Nat.one_le_iff_ne_zero.mpr h1`.

Simplify using `[h0, h1, this]`. Establish `: 1 ≤ e 0` using `Nat.one_le_iff_ne_zero.mpr h0`. Establish `h2 : e 0 - 1 + 0 + 1 = e 0` using `by omega`. Simplify using `[h0, h1, this, h2]`. Establish `h3 : 1 ≤ e 0` using `Nat.one_le_iff_ne_zero.mpr h0`.

Establish `h4 : 1 ≤ e 1` using `Nat.one_le_iff_ne_zero.mpr h1`. Establish `h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1` using `by omega`. Simplify using `[h0, h1, h3, h4, h2]`.
-/
theorem lam_mul (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X,
    coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]
  have a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0 := by simp
  have a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1 := by simp
  have a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1 := by simp
  have a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1 := by simp
  rw [a1, a2, a3, a4]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · simp [h0, h1]
  · have : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    simp [h0, h1, this]
  · have : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e 0 - 1 + 0 + 1 = e 0 := by omega
    simp [h0, h1, this, h2]
  · have h3 : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h4 : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    have h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1 := by omega
    simp [h0, h1, h3, h4, h2]

/- English proof (translation)
Establish `h` using `lam_mul wq`. Simplify using `only [nu]`. Take the linear combination `-h`.
-/
theorem wv_line1 (wq : PowerSeries ℂ_[p]) : wv wq 1 = lam wq * Xv 1 + nu wq := by
  have h := lam_mul wq
  simp only [nu]
  linear_combination -h

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]
  simp

/- English proof (translation)
Rewrite using `[lamA_coeff_wser]`. Use `split_ifs`. Conclude with `hS _`. Conclude with `S.zero_mem`.
-/
theorem lamA_wser_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by
  rw [lamA_coeff_wser]; split_ifs
  · exact hS _
  · exact S.zero_mem

/- English proof (translation)
Introduce `e`. Rewrite using `[lamA_coeff_lam]`. Conclude with `lamA_wser_mem hS _`.
-/
theorem lam_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by
  intro e
  rw [lamA_coeff_lam]
  exact lamA_wser_mem hS _

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p])` using `PowerSeries.HasSubst.X i`. Use `set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ`. Establish `hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X`. Rewrite using `[hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]`. Establish `hw : wv wq i = φ (wser wq)`.

Rewrite using `[hφ, PowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression. Rewrite using `[hX, hw]`. Establish `: G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq))`. Simplify using `only [G, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]`.

Rewrite using `[this, G_wser h, map_zero]`.
-/
theorem G_wv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (i : Fin 2) :
    G W (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wv wq i) = 0 := by
  have hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.X i
  set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ
  have hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X := by
    rw [hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  have hw : wv wq i = φ (wser wq) := by
    rw [hφ, PowerSeries.coe_substAlgHom]; rfl
  rw [hX, hw]
  have : G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq)) := by
    simp only [G, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]
  rw [this, G_wser h, map_zero]

end PI.AddIntG.Wk
