import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
open Formalism.L2.Th1.A (shortW logSer expSer fgl wpReg iSer xS IntModel)
open Formalism.L2.Th1.B (fLog lU sigS phO)

/- English proof (translation)
Introduce `K _ l hl`. Use extensionality with `n`. Unfold `Formalism.L2.Th1.CM.ltLog`. Rewrite using `[PowerSeries.coeff_mk]`. Use `split_ifs with h`.

Establish `hs` using `Nat.find_spec h conv_rhs => rw [hs]`. Rewrite using `[Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl]`. Assume the negation of the conclusion as `hc`. Conclude with `h (Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero (Ne.symm hc))`.
-/
theorem lubin_tate_log_is_artin_hasse : LtLogIsLgF := by
  intro K _ l hl
  ext n
  unfold Formalism.L2.Th1.CM.ltLog
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · have hs := Nat.find_spec h
    conv_rhs => rw [hs]
    rw [Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl]
  · by_contra hc
    exact h (Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero (Ne.symm hc))

namespace EAux

section Alg

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
The claim follows from `Pair.cc_C_mul_lgF hl ε`.
-/
theorem cc_a {l : ℕ} (hl : 2 ≤ l) (ε : K) :
    PowerSeries.constantCoeff (PowerSeries.C ε * lgF K l) = 0 :=
  Pair.cc_C_mul_lgF hl ε

/- English proof (translation)
Unfold `thetaS`. Rewrite using `[Formalism.L2.Th1.A.uSerEq K g2 g3]`.
-/
theorem thetaS_eq (l : ℕ) (g2 g3 ε : K) :
    thetaS l g2 g3 ε = PowerSeries.subst (PowerSeries.C ε * lgF K l) (expSer (shortW g2 g3)) := by
  unfold thetaS
  rw [Formalism.L2.Th1.A.uSerEq K g2 g3]

/- English proof (translation)
Rewrite using `[thetaS_eq]`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero (cc_a hl ε) _ (Formalism.L2.Th1.A.expSpec K (shortW g2 g3)).1`.
-/
theorem cc_theta {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.constantCoeff (thetaS l g2 g3 ε) = 0 := by
  rw [thetaS_eq]
  exact PowerSeries.constantCoeff_subst_eq_zero (cc_a hl ε) _
    (Formalism.L2.Th1.A.expSpec K (shortW g2 g3)).1

/- English proof (translation)
Establish `hE` using `Formalism.L2.Th1.A.expSpec K (shortW g2 g3)`. Establish `ha` using `cc_a hl ε`. Rewrite using `[thetaS_eq, Pair.ps_comp (τ := Unit) ha hE.1, hE.2.2.1, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' ha)]`.
-/
theorem log_theta {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.subst (thetaS l g2 g3 ε) (logSer (shortW g2 g3)) =
      PowerSeries.C ε * lgF K l := by
  have hE := Formalism.L2.Th1.A.expSpec K (shortW g2 g3)
  have ha := cc_a hl ε
  rw [thetaS_eq, Pair.ps_comp (τ := Unit) ha hE.1, hE.2.2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' ha)]

/- English proof (translation)
Rewrite using `[PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hb), PowerSeries.subst_C]`.
-/
theorem subst_C_mul {τ : Type} {b : MvPowerSeries τ K} (hb : MvPowerSeries.constantCoeff b = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.C c * f) = MvPowerSeries.C c * PowerSeries.subst b f := by
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hb), PowerSeries.subst_C]

end Alg

end EAux

open EAux

/- English proof (translation)
Introduce `K _ _ _ l hl _ F hF g2 g3 ε`. Establish `h2 : 2 ≤ l` using `hl.two_le`. Take `⟨hF0, -, hFc⟩` from `hF`. Establish `hE` using `Formalism.L2.Th1.A.expSpec K (shortW g2 g3)`. Establish `hθ0` using `cc_theta h2 g2 g3 ε`.

Establish `ha` using `cc_a h2 ε`. Use `⟨log_theta h2 g2 g3 ε, hθ0, ?_⟩` and prove the remaining obligations. Establish `hlog : ∀ x : Fin 2, PowerSeries.subst (at1 x (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) = MvPowerSeries.C ε * at1 x (lgF K l)`. Introduce `x`. Unfold `at1`.

Rewrite using `[Pair.ps_comp (by simp) hθ0, log_theta h2, subst_C_mul (by simp)]`. Establish `hs` using `Pair.hs2 (Pair.constantCoeff_inVar_eq_zero (0 : Fin 2) hθ0) (Pair.constantCoeff_inVar_eq_zero (1 : Fin 2) hθ0)`. Establish `hL0` using `(Formalism.L2.Th1.A.logSpec K (shortW g2 g3)).1`. Establish `hsum : MvPowerSeries.constantCoeff (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3)) + PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) = 0`. Rewrite using `[map_add, Pair.cc_ps (by simp) hL0, Pair.cc_ps (by simp) hL0, add_zero]`.

Establish `hFl : PowerSeries.subst F (lgF K l) = at1 0 (lgF K l) + at1 1 (lgF K l)`. Unfold `cob at hFc`. Rewrite `hFc` using `[sub_sub, sub_eq_zero]`. Conclude with `hFc`. Use `conv_rhs => rw [(Formalism.L2.Th1.A.fglLog K (shortW g2 g3)).2]`.

Rewrite using `[Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hsum), MvPowerSeries.subst_add hs]`. Establish `e0 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)] (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) = PowerSeries.subst (at1 0 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3))` using `Pair.subst_single_var hs (0 : Fin 2) (logSer (shortW g2 g3))`. Establish `e1 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)] (PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) = PowerSeries.subst (at1 1 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3))` using `Pair.subst_single_var hs (1 : Fin 2) (logSer (shortW g2 g3))`. Rewrite using `[e0, e1, hlog 0, hlog 1, thetaS_eq, ← Pair.ps_comp hF0 ha, subst_C_mul hF0, hFl, mul_add]`.
-/
theorem theta_homomorphism : ThetaHom := by
  intro K _ _ _ l hl _ F hF g2 g3 ε
  have h2 : 2 ≤ l := hl.two_le
  obtain ⟨hF0, -, hFc⟩ := hF
  have hE := Formalism.L2.Th1.A.expSpec K (shortW g2 g3)
  have hθ0 := cc_theta h2 g2 g3 ε
  have ha := cc_a h2 ε
  refine ⟨log_theta h2 g2 g3 ε, hθ0, ?_⟩
  have hlog : ∀ x : Fin 2, PowerSeries.subst (at1 x (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) =
      MvPowerSeries.C ε * at1 x (lgF K l) := by
    intro x
    unfold at1
    rw [Pair.ps_comp (by simp) hθ0, log_theta h2, subst_C_mul (by simp)]
  have hs := Pair.hs2 (Pair.constantCoeff_inVar_eq_zero (0 : Fin 2) hθ0) (Pair.constantCoeff_inVar_eq_zero (1 : Fin 2) hθ0)
  have hL0 := (Formalism.L2.Th1.A.logSpec K (shortW g2 g3)).1
  have hsum : MvPowerSeries.constantCoeff
      (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3)) +
        PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) = 0 := by
    rw [map_add, Pair.cc_ps (by simp) hL0, Pair.cc_ps (by simp) hL0, add_zero]
  have hFl : PowerSeries.subst F (lgF K l) = at1 0 (lgF K l) + at1 1 (lgF K l) := by
    unfold cob at hFc
    rw [sub_sub, sub_eq_zero] at hFc
    exact hFc
  conv_rhs => rw [(Formalism.L2.Th1.A.fglLog K (shortW g2 g3)).2]
  rw [Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hsum),
    MvPowerSeries.subst_add hs]
  have e0 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)]
      (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) =
      PowerSeries.subst (at1 0 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) :=
    Pair.subst_single_var hs (0 : Fin 2) (logSer (shortW g2 g3))
  have e1 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)]
      (PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) =
      PowerSeries.subst (at1 1 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) :=
    Pair.subst_single_var hs (1 : Fin 2) (logSer (shortW g2 g3))
  rw [e0, e1, hlog 0, hlog 1, thetaS_eq, ← Pair.ps_comp hF0 ha, subst_C_mul hF0, hFl, mul_add]

namespace EAux

/- English proof (translation)
Use `set θ := thetaS l g2 g3 ε with hθ`. Use `set L := logSer (shortW g2 g3) with hL`. Establish `hθ0 : PowerSeries.constantCoeff θ = 0` using `cc_theta hl g2 g3 ε`. Establish `hθL : PowerSeries.subst θ L = PowerSeries.C ε * lgF K l` using `log_theta hl g2 g3 ε`. Establish `hLs` using `Formalism.L2.Th1.A.logSpec K (shortW g2 g3)`.

Establish `hL0 : PowerSeries.constantCoeff L = 0` using `hLs.1`. Establish `hL1 : PowerSeries.coeff 1 L = 1` using `hLs.2.1`. Establish `hs` using `Formalism.L2.Th1.B.Ph.hs hθ0`. Establish `cU : PowerSeries.constantCoeff (lU L) = 1` using `(Formalism.L2.Th1.B.Ph.constantCoeff_lU L).trans hL1`. Establish `cG : PowerSeries.constantCoeff (PowerSeries.subst θ (lU L)) = 1`.

Rewrite using `[Formalism.L2.Th1.B.Ph.constantCoeff_psubst hθ0, cU]`. Establish `cl : PowerSeries.constantCoeff (lU (lgF K l)) = 1` using `(Formalism.L2.Th1.B.Ph.constantCoeff_lU _).trans (by simpa using Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl 0)`. Establish `hprod : PowerSeries.C ε⁻¹ * lU θ * PowerSeries.subst θ (lU L) = lU (lgF K l)`. Establish `h1 : PowerSeries.subst θ L = θ * PowerSeries.subst θ (lU L)` using `by conv_lhs => rw [← Formalism.L2.Th1.B.Ph.X_mul_lU hL0, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]`. Rewrite `h1` using `[hθL]`.

Establish `h2 : PowerSeries.X * (PowerSeries.C ε * lU (lgF K l)) = PowerSeries.X * (lU θ * PowerSeries.subst θ (lU L))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Formalism.L2.Th1.B.Ph.X_mul_lU hθ0]`. Use `_ = _ := by ring`. Establish `h3` using `mul_left_cancel₀ PowerSeries.X_ne_zero h2`.

Establish `hC : PowerSeries.C ε⁻¹ * PowerSeries.C ε = (1 : PowerSeries K)`. Rewrite using `[← map_mul, inv_mul_cancel₀ hε, map_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `cV : PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU θ) = 1`. Use `congrArg PowerSeries.constantCoeff hprod` as an intermediate fact.

Rewrite `this` using `[map_mul, cG, mul_one, cl]`. Conclude with `this`. Use `⟨cV, ?_⟩` and prove the remaining obligations. Establish `hlog : fLog (lU (lgF K l)) = fLog (PowerSeries.C ε⁻¹ * lU θ) + fLog (PowerSeries.subst θ (lU L))`. Rewrite using `[← hprod]`.

Conclude with `Formalism.L2.Th1.B.ParO.fLog_mul cV cG`. Establish `hcur : PowerSeries.subst θ (phCurve g2 g3 s2) = -PowerSeries.subst (PowerSeries.C ε * lgF K l) (sigS (wpReg (shortW g2 g3))) + PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 - fLog (PowerSeries.subst θ (lU L))`. Unfold `phCurve phO`. Rewrite using `[PowerSeries.subst_sub hs, PowerSeries.subst_add hs, Formalism.L2.Th1.B.Ph.psubst_neg hθ0, Formalism.L2.Th1.B.Ph.psubst_C_mul hθ0, PowerSeries.subst_pow hs, Formalism.L2.Th1.B.Ph.psubst_fLog hθ0 cU, ← Pair.ps_comp (τ := Unit) hθ0 hL0, hθL]`. Rewrite using `[hcur]`.

Unfold `phFF`. Rewrite using `[hlog]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ph_sub {K : Type} [Field K] [CharZero K] {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 : K) {ε : K}
    (hε : ε ≠ 0) :
    PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) = 1 ∧
    phFF l g2 g3 s2 ε - PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2) =
      -fLog (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) := by
  set θ := thetaS l g2 g3 ε with hθ
  set L := logSer (shortW g2 g3) with hL
  have hθ0 : PowerSeries.constantCoeff θ = 0 := cc_theta hl g2 g3 ε
  have hθL : PowerSeries.subst θ L = PowerSeries.C ε * lgF K l := log_theta hl g2 g3 ε
  have hLs := Formalism.L2.Th1.A.logSpec K (shortW g2 g3)
  have hL0 : PowerSeries.constantCoeff L = 0 := hLs.1
  have hL1 : PowerSeries.coeff 1 L = 1 := hLs.2.1
  have hs := Formalism.L2.Th1.B.Ph.hs hθ0
  have cU : PowerSeries.constantCoeff (lU L) = 1 :=
    (Formalism.L2.Th1.B.Ph.constantCoeff_lU L).trans hL1
  have cG : PowerSeries.constantCoeff (PowerSeries.subst θ (lU L)) = 1 := by
    rw [Formalism.L2.Th1.B.Ph.constantCoeff_psubst hθ0, cU]
  have cl : PowerSeries.constantCoeff (lU (lgF K l)) = 1 :=
    (Formalism.L2.Th1.B.Ph.constantCoeff_lU _).trans (by simpa using Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl 0)

  have hprod : PowerSeries.C ε⁻¹ * lU θ * PowerSeries.subst θ (lU L) = lU (lgF K l) := by
    have h1 : PowerSeries.subst θ L = θ * PowerSeries.subst θ (lU L) := by
      conv_lhs => rw [← Formalism.L2.Th1.B.Ph.X_mul_lU hL0, PowerSeries.subst_mul hs,
        PowerSeries.subst_X hs]
    rw [hθL] at h1
    have h2 : PowerSeries.X * (PowerSeries.C ε * lU (lgF K l)) =
        PowerSeries.X * (lU θ * PowerSeries.subst θ (lU L)) := by
      calc PowerSeries.X * (PowerSeries.C ε * lU (lgF K l))
          = PowerSeries.C ε * (PowerSeries.X * lU (lgF K l)) := by ring
        _ = PowerSeries.C ε * lgF K l := by rw [Formalism.L2.Th1.B.Ph.X_mul_lU (Pair.cc_lgF hl)]
        _ = θ * PowerSeries.subst θ (lU L) := h1
        _ = (PowerSeries.X * lU θ) * PowerSeries.subst θ (lU L) := by
            rw [Formalism.L2.Th1.B.Ph.X_mul_lU hθ0]
        _ = _ := by ring
    have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
    have hC : PowerSeries.C ε⁻¹ * PowerSeries.C ε = (1 : PowerSeries K) := by
      rw [← map_mul, inv_mul_cancel₀ hε, map_one]
    calc PowerSeries.C ε⁻¹ * lU θ * PowerSeries.subst θ (lU L)
        = PowerSeries.C ε⁻¹ * (lU θ * PowerSeries.subst θ (lU L)) := by ring
      _ = PowerSeries.C ε⁻¹ * PowerSeries.C ε * lU (lgF K l) := by rw [← h3]; ring
      _ = _ := by rw [hC, one_mul]
  have cV : PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU θ) = 1 := by
    have := congrArg PowerSeries.constantCoeff hprod
    rw [map_mul, cG, mul_one, cl] at this
    exact this
  refine ⟨cV, ?_⟩
  have hlog : fLog (lU (lgF K l)) =
      fLog (PowerSeries.C ε⁻¹ * lU θ) + fLog (PowerSeries.subst θ (lU L)) := by
    rw [← hprod]
    exact Formalism.L2.Th1.B.ParO.fLog_mul cV cG
  have hcur : PowerSeries.subst θ (phCurve g2 g3 s2) =
      -PowerSeries.subst (PowerSeries.C ε * lgF K l) (sigS (wpReg (shortW g2 g3))) +
        PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 -
        fLog (PowerSeries.subst θ (lU L)) := by
    unfold phCurve phO
    rw [PowerSeries.subst_sub hs, PowerSeries.subst_add hs, Formalism.L2.Th1.B.Ph.psubst_neg hθ0,
      Formalism.L2.Th1.B.Ph.psubst_C_mul hθ0, PowerSeries.subst_pow hs,
      Formalism.L2.Th1.B.Ph.psubst_fLog hθ0 cU, ← Pair.ps_comp (τ := Unit) hθ0 hL0, hθL]
  rw [hcur]
  unfold phFF
  rw [hlog]
  ring

/- English proof (translation)
Introduce `n`. Establish `hn : n = Finsupp.single () (n ())`. Use `ext`. Simplify using the standard rewrite rules. Establish `e : MvPowerSeries.coeff n (PowerSeries.C ε⁻¹ * lU θ) = ε⁻¹ * PowerSeries.coeff (n () + 1) θ` using `by conv_lhs => rw [hn]`.

Express the relevant statement in the definitionally equal form `PowerSeries.coeff (n ()) (PowerSeries.C ε⁻¹ * lU θ) = _`. Rewrite using `[PowerSeries.coeff_C_mul, lU, PowerSeries.coeff_mk]`. Rewrite using `[e, norm_mul, norm_inv, hε, inv_one, one_mul]`. Conclude with `hθ _`.
-/
theorem integral_V {K : Type} [NormedField K] {ε : K} (hε : ‖ε‖ = 1) {θ : PowerSeries K}
    (hθ : ∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) :
    Integral (ι := Unit) (PowerSeries.C ε⁻¹ * lU θ) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext
    simp
  have e : MvPowerSeries.coeff n (PowerSeries.C ε⁻¹ * lU θ) =
      ε⁻¹ * PowerSeries.coeff (n () + 1) θ := by
    conv_lhs => rw [hn]
    change PowerSeries.coeff (n ()) (PowerSeries.C ε⁻¹ * lU θ) = _
    rw [PowerSeries.coeff_C_mul, lU, PowerSeries.coeff_mk]
  rw [e, norm_mul, norm_inv, hε, inv_one, one_mul]
  exact hθ _

/- English proof (translation)
Establish `hle : ‖(2 : K)‖ ≤ 1` using `by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2`. Use `le_antisymm hle ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Take `⟨m, hm⟩` from `hp.odd_of_ne_two h2.ne'`.

Establish `e : (1 : K) = (l : K) - 2 * (m : K)`. Rewrite using `[hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hl1 : ‖(l : K)‖ < 1`.

Rewrite using `[hn]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `hm1 : ‖(2 : K) * (m : K)‖ < 1`. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)) hlt`.

Establish `: ‖(1 : K)‖ < 1`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (by rw [sub_eq_add_neg, ← norm_neg (2 * (m : K))]; exact IsUltrametricDist.norm_add_le_max _ _) (max_lt hl1 hm1)`. Rewrite `this` using `[norm_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] {l : ℕ} (hp : l.Prime)
    (h2 : 2 < l) (hn : ‖(l : K)‖ = (l : ℝ)⁻¹) : ‖(2 : K)‖ = 1 := by
  have hle : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
  refine le_antisymm hle ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two h2.ne'
  have e : (1 : K) = (l : K) - 2 * (m : K) := by
    rw [hm]
    push_cast
    ring
  have hl1 : ‖(l : K)‖ < 1 := by
    rw [hn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hm1 : ‖(2 : K) * (m : K)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K m)) hlt
  have : ‖(1 : K)‖ < 1 := by
    rw [e]
    exact lt_of_le_of_lt (by rw [sub_eq_add_neg, ← norm_neg (2 * (m : K))]; exact IsUltrametricDist.norm_add_le_max _ _)
      (max_lt hl1 hm1)
  rw [norm_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h4 : ‖(4 : K)‖ = 1`. Establish `: (4 : K) = 2 * 2` using `by norm_num`. Rewrite using `[this, norm_mul, ht, mul_one]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[shortW]`.

Simplify using `[shortW]`. Simplify using `[shortW]`. Simplify `h2` using `[shortW, h4]`. Simplify `h3` using `[shortW, h4]`.
-/
theorem intModel {K : Type} [NormedField K] {g2 g3 : K} (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (ht : ‖(2 : K)‖ = 1) : IntModel (shortW g2 g3) := by
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, ht, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [shortW]
  · simp [shortW]
  · simp [shortW]
  · simpa [shortW, h4] using h2
  · simpa [shortW, h4] using h3

end EAux

/- English proof (translation)
Introduce `K _ _ _ l hl g2 g3 s2 ε hε hθ`. Establish `hε0 : ε ≠ 0`. Introduce `h`. Rewrite `hε` using `[h, norm_zero]`. Conclude with `zero_ne_one hε`.

Take `⟨cV, hsub⟩` from `ph_sub hl.two_le g2 g3 s2 hε0`. Establish `h` using `(Formalism.L2.Th1.B.simeqLog K Unit _ cV (integral_V hε hθ)).2`. Unfold `Simeq at h ⊢`. Rewrite `h` using `[sub_zero]`. Establish `e : (phFF l g2 g3 s2 ε : MvPowerSeries Unit K) - PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2) = -fLog (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε))` using `hsub`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem phi_comparison : PhCompare := by
  intro K _ _ _ l hl g2 g3 s2 ε hε hθ
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hε
    exact zero_ne_one hε
  obtain ⟨cV, hsub⟩ := ph_sub hl.two_le g2 g3 s2 hε0
  have h := (Formalism.L2.Th1.B.simeqLog K Unit _ cV (integral_V hε hθ)).2
  unfold Simeq at h ⊢
  rw [sub_zero] at h
  have e : (phFF l g2 g3 s2 ε : MvPowerSeries Unit K) -
      PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2) =
      -fLog (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) := hsub
  rw [e]
  exact h

/- English proof (translation)
Introduce `K _ _ _ l hl h2l hn F hF g2 g3 s2 ε hg2 hg3 hε hθ`. Establish `ht` using `norm_two hl h2l hn`. Establish `hW` using `intModel hg2 hg3 ht`. Take `⟨hLaw, hInv, -⟩` from `Formalism.L2.Th1.A.bridgeLaw K (shortW g2 g3) hW`. Establish `hO` using `Formalism.L2.Th1.B.f1O K _ _ s2 _ _ _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K (shortW g2 g3)) hLaw hInv (Formalism.L2.Th1.A.bridgeCurve K (shortW g2 g3) hW) ht`.

Conclude with `transport_first_level K l hl hn F hF (fgl (shortW g2 g3)) (thetaS l g2 g3 ε) (phCurve g2 g3 s2) (phFF l g2 g3 s2 ε) hLaw.1 hθ (theta_homomorphism K l hl hn F hF g2 g3 ε).2 ⟨hO.1, hO.2.2.1, hO.2.2.2⟩ (phi_comparison K l hl g2 g3 s2 ε hε hθ)`.
-/
theorem first_level_curve_holds : CurveExponentCoboundaryCocycle := by
  intro K _ _ _ l hl h2l hn F hF g2 g3 s2 ε hg2 hg3 hε hθ
  have ht := norm_two hl h2l hn
  have hW := intModel hg2 hg3 ht
  obtain ⟨hLaw, hInv, -⟩ := Formalism.L2.Th1.A.bridgeLaw K (shortW g2 g3) hW
  have hO := Formalism.L2.Th1.B.f1O K _ _ s2 _ _ _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K (shortW g2 g3))
    hLaw hInv (Formalism.L2.Th1.A.bridgeCurve K (shortW g2 g3) hW) ht
  exact transport_first_level K l hl hn F hF (fgl (shortW g2 g3)) (thetaS l g2 g3 ε) (phCurve g2 g3 s2)
    (phFF l g2 g3 s2 ε) hLaw.1 hθ (theta_homomorphism K l hl hn F hF g2 g3 ε).2
    ⟨hO.1, hO.2.2.1, hO.2.2.2⟩ (phi_comparison K l hl g2 g3 s2 ε hε hθ)

/- English proof (translation)
Introduce `K _ _ _ l d _ σ hU hd hev F hF g2 g3 s2 ε hg2 hg3 hε hθ ι _ om oms hO ζ hζ`. Conclude with `biextension_hypotheses_of_level_one K l d σ hU hd hev F hF _ (first_level_curve_holds K l hU.1 hU.2.1 hU.2.2.1 F hF g2 g3 s2 ε hg2 hg3 hε hθ) ι om oms hO ζ hζ`.
-/
theorem biextension_hypotheses_curve : BHypCurve := by
  intro K _ _ _ l d _ σ hU hd hev F hF g2 g3 s2 ε hg2 hg3 hε hθ ι _ om oms hO ζ hζ
  exact biextension_hypotheses_of_level_one K l d σ hU hd hev F hF _
    (first_level_curve_holds K l hU.1 hU.2.1 hU.2.2.1 F hF g2 g3 s2 ε hg2 hg3 hε hθ) ι om oms hO ζ hζ

end Formalism.L2.Th1.D
