import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.GlobalTheory.GL3.ExistsTorsionPointOfLattice
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section

namespace Formalism.L2.KerInert.Sigma

open NumberField Formalism.BasicNotions

/- English proof (translation)
Unfold `Formalism.MainNotions.TaylorLogMetric.lamC`. Rewrite using `[dif_pos a.2]`.
-/
theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (a : Formalism.MainNotions.TaylorLogMetric.Qbar) :
    Formalism.MainNotions.TaylorLogMetric.lamC lam (a : ℂ) = lam a := by
  unfold Formalism.MainNotions.TaylorLogMetric.lamC
  rw [dif_pos a.2]

/- English proof (translation)
Rewrite using `[Formalism.L2.Th1.F.taylorSgStar L, Formalism.L2.Th1.F.pOfLattice L, h2, h3, hs]`. Establish `hm` using `Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) a2 a3 s0 (Formalism.L2.Th1.F.pOf a2 a3)`. Rewrite using `[hm.2.2.2.2.2, hm.2.2.1]`. Both sides reduce to the same expression.
-/
theorem taylor_sgStar_map (L : PeriodPair) (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3)
    (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.sgStar L) =
      PowerSeries.map (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
  rw [Formalism.L2.Th1.F.taylorSgStar L, Formalism.L2.Th1.F.pOfLattice L, h2, h3, hs]
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) a2 a3 s0
    (Formalism.L2.Th1.F.pOf a2 a3)
  rw [hm.2.2.2.2.2, hm.2.2.1]
  rfl

/- English proof (translation)
Establish `hT` using `taylor_sgStar_map L a2 a3 s0 h2 h3 hs`. Establish `e : Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup = PowerSeries.map lam (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3))`. Use extensionality with `n`. Establish `hn` using `congrArg (PowerSeries.coeff n) hT`. Unfold `Formalism.L2.Th1.F.taylor0 at hn`.

Rewrite `hn` using `[PowerSeries.coeff_mk, PowerSeries.coeff_map]`. Unfold `Formalism.MainNotions.TaylorLogMetric.sgSer`. Rewrite using `[PowerSeries.coeff_mk, PowerSeries.coeff_map, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA.sgStar_eq L, hn]`. Conclude with `lamC_coe lam _`. Establish `hm` using `Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ_[p] lam a2 a3 s0 (Formalism.L2.Th1.F.pOf a2 a3)`.

Rewrite using `[e, hm.2.2.2.2.2, hm.2.2.1]`.
-/
theorem sgSer_eq {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (L : PeriodPair)
    (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3) (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      Formalism.L2.Th1.B.sgStar (lam s0) (Formalism.L2.Th1.F.pOf (lam a2) (lam a3)) := by
  have hT := taylor_sgStar_map L a2 a3 s0 h2 h3 hs
  have e : Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      PowerSeries.map lam (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
    ext n
    have hn := congrArg (PowerSeries.coeff n) hT
    unfold Formalism.L2.Th1.F.taylor0 at hn
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map] at hn
    unfold Formalism.MainNotions.TaylorLogMetric.sgSer
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA.sgStar_eq L, hn]
    exact lamC_coe lam _
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ_[p] lam a2 a3 s0 (Formalism.L2.Th1.F.pOf a2 a3)
  rw [e, hm.2.2.2.2.2, hm.2.2.1]

/- English proof (translation)
Establish `e4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4) = -(lam a2) / 4`. Establish `: -(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ)` using `by rw [h2]; push_cast; rfl`. Rewrite using `[this, lamC_coe, map_div₀, map_neg, map_ofNat]`. Establish `e6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4) = -(lam a3) / 4`. Establish `: -(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ)` using `by rw [h3]; push_cast; rfl`.

Rewrite using `[this, lamC_coe, map_div₀, map_neg, map_ofNat]`. Simplify using `only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, Formalism.MainNotions.TaylorLogMetric.wModel, e4, e6]`. Apply the tactic sequence `constructor <;> ring`.
-/
theorem wModel_g {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (a2 a3 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = a2) (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = a3) :
    Formalism.L2.Th1.A.g₂ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a2 ∧ Formalism.L2.Th1.A.g₃ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a3 := by
  have e4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4) = -(lam a2) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h2]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  have e6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4) = -(lam a3) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h3]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, Formalism.MainNotions.TaylorLogMetric.wModel, e4, e6]
  constructor <;> ring

/- English proof (translation)
Simplify using `only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆]`. Apply the tactic sequence `constructor <;> ring`.
-/
theorem g_change {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) :
    Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
      Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆]
  constructor <;> ring

/- English proof (translation)
The claim follows from `Formalism.L2.Th1.F.isWpUnique K _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K W) (Formalism.L2.Th1.F.pOfIsWp K _ _)`.
-/
theorem wpReg_eq {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    Formalism.L2.Th1.A.wpReg W = Formalism.L2.Th1.F.pOf (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) :=
  Formalism.L2.Th1.F.isWpUnique K _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K W) (Formalism.L2.Th1.F.pOfIsWp K _ _)

section Int

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hle : Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} ≤ (Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1}).toSubring`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `ζ ⟨n, hn, hc, hz⟩`. Conclude with `Subfield.subset_closure ⟨n, hn, (Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm, hz⟩`.

Establish `hsub : ((Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} : Subring ℂ_[p]) : Set ℂ_[p]) ⊆ ((Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1} : Subfield ℂ_[p]) : Set ℂ_[p])` using `fun y hy => hle hy`. Conclude with `closure_mono hsub hx`.
-/
theorem wp_sub_kur (x : ℂ_[p]) (hx : x ∈ Formalism.MainNotions.GL3Theta.Wp p) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p := by
  have hp : p.Prime := Fact.out
  have hle : Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1}).toSubring := by
    rw [Subring.closure_le]
    rintro ζ ⟨n, hn, hc, hz⟩
    exact Subfield.subset_closure ⟨n, hn, (Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm, hz⟩
  have hsub : ((Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} : Subring ℂ_[p]) :
      Set ℂ_[p]) ⊆ ((Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1} : Subfield ℂ_[p]) :
      Set ℂ_[p]) := fun y hy => hle hy
  exact closure_mono hsub hx

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)`.
-/
theorem nadd {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/- English proof (translation)
Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hx (norm_nonneg _) hy`.
-/
theorem nmul {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])`.
-/
theorem nsub {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one ℂ_[p] n`.
-/
theorem nnat (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

/- English proof (translation)
Use `nnat (p := p) (OfNat.ofNat n)` as an intermediate fact. Rewrite `this` using `[Nat.cast_ofNat]`. Then use the resulting hypothesis.
-/
theorem nofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := nnat (p := p) (OfNat.ofNat n); rwa [Nat.cast_ofNat] at this

/- English proof (translation)
Introduce `h`. Break down `(Nat.Prime.dvd_mul hp).1 h with h | h` into its components or cases. Use `Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega` as an intermediate fact. Use `Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega` as an intermediate fact.
-/
theorem not_dvd_23 (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Use `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (not_dvd_23 hp h5 2 1)` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`.
-/
theorem padic_norm_twelve_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(12 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 2 1)
  norm_num at this
  exact this

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Use `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (not_dvd_23 hp h5 3 3)` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`.
-/
theorem padicNorm_twoHundredSixteen_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(216 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 3 3)
  norm_num at this
  exact this

/- English proof (translation)
Establish `k1` using `wp_sub_kur _ w1`. Establish `k2` using `wp_sub_kur _ w2`. Establish `k3` using `wp_sub_kur _ w3`. Establish `k4` using `wp_sub_kur _ w4`. Establish `k6` using `wp_sub_kur _ w6`.

Establish `hb2 : W.b₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₂‖ ≤ 1`. Unfold `WeierstrassCurve.b₂`. Conclude with `⟨add_mem (pow_mem k1 2) (mul_mem (ofNat_mem _ 4) k2), nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i1) (nmul (nofNat 4) i2)⟩`. Establish `hb4 : W.b₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₄‖ ≤ 1`. Unfold `WeierstrassCurve.b₄`.

Conclude with `⟨add_mem (mul_mem (ofNat_mem _ 2) k4) (mul_mem k1 k3), nadd (nmul (nofNat 2) i4) (nmul i1 i3)⟩`. Establish `hb6 : W.b₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₆‖ ≤ 1`. Unfold `WeierstrassCurve.b₆`. Conclude with `⟨add_mem (pow_mem k3 2) (mul_mem (ofNat_mem _ 4) k6), nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i3) (nmul (nofNat 4) i6)⟩`. Take `⟨m2, n2⟩` from `hb2`.

Take `⟨m4, n4⟩` from `hb4`. Take `⟨m6, n6⟩` from `hb6`. Establish `hc4 : W.c₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₄‖ ≤ 1`. Unfold `WeierstrassCurve.c₄`. Conclude with `⟨sub_mem (pow_mem m2 2) (mul_mem (ofNat_mem _ 24) m4), nsub (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2) (nmul (nofNat 24) n4)⟩`.

Establish `hc6 : W.c₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₆‖ ≤ 1`. Unfold `WeierstrassCurve.c₆`. Conclude with `⟨sub_mem (add_mem (neg_mem (pow_mem m2 3)) (mul_mem (mul_mem (ofNat_mem _ 36) m2) m4)) (mul_mem (ofNat_mem _ 216) m6), nsub (nadd (by rw [norm_neg, norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2) (nmul (nmul (nofNat 36) n2) n4)) (nmul (nofNat 216) n6)⟩`. Establish `e12` using `padic_norm_twelve_eq_one_of_five_le (p := p) h5`. Establish `e216` using `padicNorm_twoHundredSixteen_eq_one_of_five_le (p := p) h5`.

Establish `h12 : (12 : ℂ_[p]) ≠ 0` using `by intro h; rw [h, norm_zero] at e12; exact zero_ne_one e12`. Establish `h216 : (216 : ℂ_[p]) ≠ 0` using `by intro h; rw [h, norm_zero] at e216; exact zero_ne_one e216`. Use `⟨div_mem hc4.1 (ofNat_mem _ 12), div_mem hc6.1 (ofNat_mem _ 216), ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.Th1.A.g₂`. Rewrite using `[norm_div, e12, div_one]`.

Conclude with `hc4.2`. Unfold `Formalism.L2.Th1.A.g₃`. Rewrite using `[norm_div, e216, div_one]`. Conclude with `hc6.2`. Establish `hrel` using `W.c_relation`.

Establish `e : Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2 = W.Δ`. Unfold `Formalism.L2.Th1.A.g₂ Formalism.L2.Th1.A.g₃`. Establish `h1728 : (1728 : ℂ_[p]) = 12 ^ 3` using `by norm_num`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(216 : ℂ_[p]) ^ 2 * 12 ^ 3 / 1728 + 0) * hrel`.

Rewrite using `[e, hΔ]`.
-/
theorem inv_good (W : WeierstrassCurve ℂ_[p]) (h5 : 5 ≤ p) (i1 : ‖W.a₁‖ ≤ 1) (i2 : ‖W.a₂‖ ≤ 1)
    (i3 : ‖W.a₃‖ ≤ 1) (i4 : ‖W.a₄‖ ≤ 1) (i6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1)
    (w1 : W.a₁ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w2 : W.a₂ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w3 : W.a₃ ∈ Formalism.MainNotions.GL3Theta.Wp p)
    (w4 : W.a₄ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w6 : W.a₆ ∈ Formalism.MainNotions.GL3Theta.Wp p) :
    Formalism.L2.Th1.A.g₂ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ Formalism.L2.Th1.A.g₃ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
      ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 1 ∧ ‖Formalism.L2.Th1.A.g₃ W‖ ≤ 1 ∧
      ‖Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2‖ = 1 := by
  have k1 := wp_sub_kur _ w1
  have k2 := wp_sub_kur _ w2
  have k3 := wp_sub_kur _ w3
  have k4 := wp_sub_kur _ w4
  have k6 := wp_sub_kur _ w6
  have hb2 : W.b₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₂‖ ≤ 1 := by
    unfold WeierstrassCurve.b₂
    exact ⟨add_mem (pow_mem k1 2) (mul_mem (ofNat_mem _ 4) k2),
      nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i1) (nmul (nofNat 4) i2)⟩
  have hb4 : W.b₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₄‖ ≤ 1 := by
    unfold WeierstrassCurve.b₄
    exact ⟨add_mem (mul_mem (ofNat_mem _ 2) k4) (mul_mem k1 k3), nadd (nmul (nofNat 2) i4) (nmul i1 i3)⟩
  have hb6 : W.b₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.b₆‖ ≤ 1 := by
    unfold WeierstrassCurve.b₆
    exact ⟨add_mem (pow_mem k3 2) (mul_mem (ofNat_mem _ 4) k6),
      nadd (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) i3) (nmul (nofNat 4) i6)⟩
  obtain ⟨m2, n2⟩ := hb2
  obtain ⟨m4, n4⟩ := hb4
  obtain ⟨m6, n6⟩ := hb6
  have hc4 : W.c₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₄‖ ≤ 1 := by
    unfold WeierstrassCurve.c₄
    exact ⟨sub_mem (pow_mem m2 2) (mul_mem (ofNat_mem _ 24) m4),
      nsub (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2) (nmul (nofNat 24) n4)⟩
  have hc6 : W.c₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ ‖W.c₆‖ ≤ 1 := by
    unfold WeierstrassCurve.c₆
    exact ⟨sub_mem (add_mem (neg_mem (pow_mem m2 3)) (mul_mem (mul_mem (ofNat_mem _ 36) m2) m4))
        (mul_mem (ofNat_mem _ 216) m6),
      nsub (nadd (by rw [norm_neg, norm_pow]; exact pow_le_one₀ (norm_nonneg _) n2)
        (nmul (nmul (nofNat 36) n2) n4)) (nmul (nofNat 216) n6)⟩
  have e12 := padic_norm_twelve_eq_one_of_five_le (p := p) h5
  have e216 := padicNorm_twoHundredSixteen_eq_one_of_five_le (p := p) h5
  have h12 : (12 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at e12; exact zero_ne_one e12
  have h216 : (216 : ℂ_[p]) ≠ 0 := by intro h; rw [h, norm_zero] at e216; exact zero_ne_one e216
  refine ⟨div_mem hc4.1 (ofNat_mem _ 12), div_mem hc6.1 (ofNat_mem _ 216), ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂; rw [norm_div, e12, div_one]; exact hc4.2
  · unfold Formalism.L2.Th1.A.g₃; rw [norm_div, e216, div_one]; exact hc6.2
  · have hrel := W.c_relation
    have e : Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2 = W.Δ := by
      unfold Formalism.L2.Th1.A.g₂ Formalism.L2.Th1.A.g₃
      have h1728 : (1728 : ℂ_[p]) = 12 ^ 3 := by norm_num
      field_simp
      linear_combination (-(216 : ℂ_[p]) ^ 2 * 12 ^ 3 / 1728 + 0) * hrel
    rw [e, hΔ]

end Int

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Establish `hd0 : 0 < dK` using `by omega`. Take `⟨S, hS, -, -, hsum⟩` from `Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0`. Take `⟨hst, hns⟩` from `Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2`. Rewrite `hsum` using `[Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns]`.

Establish `hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P`. Rewrite using `[← hsum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l`.

Introduce `P hPS`. Take `⟨h1, h2⟩` from `hS.1 P hPS`. Establish `h3 : (dK : ℂ) * P ∈ L.lattice`. Establish `h4'` using `hst _ h1`. Establish `h5 : (dK : ℂ) * P = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P))`.

Rewrite using `[← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h5]`. Conclude with `neg_mem h4'`. Conclude with `(Formalism.L2.Th1.CM.cm4 dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1`.

Establish `hn : ¬ l ∣ 2 * dK`. Introduce `h`. Break down `(Nat.Prime.dvd_mul hlp).1 h with h | h` into its components or cases. Use `Nat.le_of_dvd (by norm_num) h; omega` as an intermediate fact. Conclude with `hld h`.

Establish `hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1` using `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn`. Establish `hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0`. Introduce `h`. Rewrite `hN` using `[h, norm_zero]`. Conclude with `zero_ne_one hN`.

Establish `key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P))`. Establish `h` using `congrArg ι hsum'`. Rewrite `h` using `[map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast]`. Rewrite using `[← Finset.mul_sum, ← h]`. Use `push_cast`.

Move the coercions through the operations in `at hN0`. Establish `hd : (dK : ℂ_[l]) ≠ 0` using `right_ne_zero_of_mul hN0`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))`.
-/
theorem s2_in_unramified_closure (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (h4 : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]) (hlam : lam ≠ 0)
    (k2 : lam ^ 4 * ι L.g₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (k3 : lam ^ 6 * ι L.g₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l)
    (n2 : ‖lam ^ 4 * ι L.g₂‖ ≤ 1) (n3 : ‖lam ^ 6 * ι L.g₃‖ ≤ 1)
    (nd : ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1) :
    lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hlp : l.Prime := Fact.out
  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring
  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4' := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4'
    exact (Formalism.L2.Th1.CM.cm4 dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'
    rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))

/- English proof (translation)
Introduce `D p _ cc δ g hAt h5 hIn hOW`. Take `⟨hcurve, -, hδ12, hLam, hOk⟩` from `hAt`. Establish `hcc : cc ≠ ⊥` using `hcurve.1`. Establish `hδ : δ ≠ 0`. Introduce `h0`.

Take `⟨⟨L1, hL1⟩, -⟩` from `Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)`. Establish `hd` using `Formalism.L2.Th1.F.discNeZero L1`. Apply `hd` to reduce the goal to its premises. Establish `h12` using `hδ12`.

Unfold `Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12`. Rewrite `h12` using `[h0, e2, e3]`. Rewrite using `[← h12]`. Evaluate the numerical expressions. Take `⟨⟨L, hL⟩, hCM⟩` from `Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ`.

Establish `hLg : g.abelian₂ = L.lattice.toAddSubgroup` using `hLam.trans hL.symm`. Take `⟨hg2, hg3⟩` from `hInv D cc δ hcurve hδ12 L hL`. Establish `hs` using `hS2 D cc δ hcurve hδ12 L hL`. Use `set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2`. Use `set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3`.

Use `set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)`. Establish `hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ = Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3))`. Rewrite using `[hLg]`. Conclude with `sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl`.

Establish `hW0` using `wModel_g g.lam g.abelian₂ a2 a3 e2 e3`. Use `set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε`. Establish `hεne : ε ≠ 0` using `Units.ne_zero _`. Take `⟨c2, c3⟩` from `g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)`. Establish `gW2 : Formalism.L2.Th1.A.g₂ g.W = ε ^ 4 * g.lam a2` using `by rw [← hW0.1]; exact c2`.

Establish `gW3 : Formalism.L2.Th1.A.g₃ g.W = ε ^ 6 * g.lam a3` using `by rw [← hW0.2]; exact c3`. Establish `hwp : Formalism.L2.Th1.A.wpReg g.W = PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3))`. Rewrite using `[wpReg_eq, gW2, gW3]`. Conclude with `(Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1`. Use `⟨ε ^ 2 * g.lam s0, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨ι, hι⟩` from `Formalism.L2.KerInert.lamExt p g.lam`. Establish `hp : p.Prime` using `Fact.out`. Establish `hdp : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hd4 : D.host.d % 4 = 3` using `by have := D.host.hyp.2.2.2.1; omega`. Establish `hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p)` using `ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn`.

Establish `hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p)`. Introduce and unpack `⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩`. Establish `hpd : ¬ p ∣ D.host.d`. Introduce `h`. Apply `hsq'` to reduce the goal to its premises.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[(ZMod.natCast_eq_zero_iff _ _).2 h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L`. Introduce `ω hω`.

Establish `h1` using `hCM ω (by rw [← hL]; exact hω)`. Rewrite `h1` using `[← hL]`. Establish `e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d`. Unfold `Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`. Establish `hιg2 : ι L.g₂ = g.lam a2` using `hι a2`. Establish `hιg3 : ι L.g₃ = g.lam a3` using `hι a3`.

Establish `hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0` using `hι s0`. Take `⟨i1, i2, i3, i4, i6, hΔ⟩` from `hOk.1`. Take `⟨w1, w2, w3, w4, w6⟩` from `hOW`. Take `⟨k2, k3, n2, n3, nd⟩` from `inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6`. Rewrite `k2`, `n2` using `[gW2, ← hιg2]`.

Rewrite `k3`, `n3` using `[gW3, ← hιg3]`. Rewrite `nd` using `[gW2, gW3, ← hιg2, ← hιg3]`. Rewrite using `[← hιs]`. Conclude with `s2_in_unramified_closure D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι ε hεne k2 k3 n2 n3 nd`. Unfold `Formalism.L2.Th1.B.sgW`.

Rewrite using `[hser, hwp]`. Conclude with `((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm`.
-/
theorem sigmaCurveInert_of (hInv : InvAlg) (hS2 : SecondEisensteinAlgebraic) : Formalism.L2.KerInert.Dict.SigmaCurveInert := by
  intro D p _ cc δ g hAt h5 hIn hOW
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hAt
  have hcc : cc ≠ ⊥ := hcurve.1

  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num

  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)

  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hεne : ε ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = ε ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = ε ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [wpReg_eq, gW2, gW3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1
  refine ⟨ε ^ 2 * g.lam s0, ?_, ?_⟩
  ·
    obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
    have hp : p.Prime := Fact.out
    have hdp : D.host.d.Prime := D.host.hyp.2.1
    have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
    have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
    have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
      rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
    have hpd : ¬ p ∣ D.host.d := by
      intro h; apply hsq'; refine ⟨0, ?_⟩
      rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
    have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
      intro ω hω
      have h1 := hCM ω (by rw [← hL]; exact hω)
      rw [← hL] at h1
      have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
        unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
      rw [e]; exact h1
    have hιg2 : ι L.g₂ = g.lam a2 := hι a2
    have hιg3 : ι L.g₃ = g.lam a3 := hι a3
    have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
    obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
    obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
    obtain ⟨k2, k3, n2, n3, nd⟩ := inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
    rw [gW2, ← hιg2] at k2 n2
    rw [gW3, ← hιg3] at k3 n3
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd
    rw [← hιs]
    exact s2_in_unramified_closure D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι ε hεne k2 k3 n2 n3 nd
  ·
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm

end Formalism.L2.KerInert.Sigma
