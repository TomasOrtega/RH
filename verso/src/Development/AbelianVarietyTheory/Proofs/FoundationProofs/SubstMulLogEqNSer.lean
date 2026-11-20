import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.InvariantDifferentialMulEqDerivX
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.IntDLog

open PowerSeries Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

def intModel (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    WeierstrassCurve (Formalism.G.unitBall ℂ_[p]) :=
  ⟨⟨g.W.a₁, h.1⟩, ⟨g.W.a₂, h.2.1⟩, ⟨g.W.a₃, h.2.2.1⟩, ⟨g.W.a₄, h.2.2.2.1⟩, ⟨g.W.a₆, h.2.2.2.2⟩⟩

/- English proof (translation)
Apply the tactic sequence `ext <;> rfl`.
-/
theorem intModel_map (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    (intModel g h).map (Formalism.G.unitBall ℂ_[p]).subtype = g.W := by
  ext <;> rfl

/- English proof (translation)
Establish `hl : g.l = Formalism.L2.Th1.A.logSer g.W` using `Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1`. Establish `he : g.ex = Formalism.L2.Th1.A.expSer g.W` using `Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk`. Take `⟨hl0, -, -, -⟩` from `Formalism.L2.Th1.A.logSpec ℂ_[p] g.W`. Take `⟨he0, -, hLE, -, -⟩` from `Formalism.L2.Th1.A.expSpec ℂ_[p] g.W`. Proceed by induction on `N with`.

Consider the case `zero`. Simplify using `only [Nat.cast_zero, map_zero, zero_mul]`. Rewrite using `[he]`. Conclude with `PowerSeries.subst_zero_of_constantCoeff_zero he0`. Consider the case `succ N ih`.

Establish `hcN : PowerSeries.constantCoeff (Formalism.L2.Th1.A.nSer g.W N) = 0` using `Formalism.L2.Th1.A.ZSer.nSer_cc g.W N`. Establish `hadd` using `Formalism.L2.KerInert.Dict.formal_addition_agree p g hOk Unit (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) (Formalism.L2.Th1.A.nSer g.W N) (MvPowerSeries.constantCoeff_X _) hcN`. Establish `hN : PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l = PowerSeries.C (N : ℂ_[p]) * g.l`. Establish `hb : HasSubst (PowerSeries.C (N : ℂ_[p]) * g.l)` using `HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl, hl0, mul_zero])`. Establish `hex : HasSubst g.ex` using `HasSubst.of_constantCoeff_zero' (by rw [he]; exact he0)`.

Establish `hLE' : PowerSeries.subst g.ex g.l = PowerSeries.X` using `by rw [he, hl]; exact hLE`. Rewrite using `[← ih, ← PowerSeries.subst_comp_subst_apply hex hb g.l, hLE', PowerSeries.subst_X hb]`. Use `show _ = MvPowerSeries.subst (![PowerSeries.X, Formalism.L2.Th1.A.nSer g.W N] : Fin 2 → PowerSeries ℂ_[p]) (Formalism.L2.Th1.A.fgl g.W)`. Rewrite using `[← hadd]`. Use `show _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l + PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l) g.ex`.

Rewrite using `[hN, PowerSeries.X_subst]`. Use `congr 1`. Use `push_cast`. Rewrite using `[map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subst_mul_log_eq_nSer (g : G1 p) (hOk : g.Ok) (N : ℕ) :
    (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p]) =
      Formalism.L2.Th1.A.nSer g.W N := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  obtain ⟨he0, -, hLE, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  induction N with
  | zero =>
    simp only [Nat.cast_zero, map_zero, zero_mul]
    rw [he]
    exact PowerSeries.subst_zero_of_constantCoeff_zero he0
  | succ N ih =>
    have hcN : PowerSeries.constantCoeff (Formalism.L2.Th1.A.nSer g.W N) = 0 :=
      Formalism.L2.Th1.A.ZSer.nSer_cc g.W N
    have hadd := Formalism.L2.KerInert.Dict.formal_addition_agree p g hOk Unit
      (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) (Formalism.L2.Th1.A.nSer g.W N) (MvPowerSeries.constantCoeff_X _) hcN
    have hN : PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l = PowerSeries.C (N : ℂ_[p]) * g.l := by
      have hb : HasSubst (PowerSeries.C (N : ℂ_[p]) * g.l) :=
        HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl, hl0, mul_zero])
      have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' (by rw [he]; exact he0)
      have hLE' : PowerSeries.subst g.ex g.l = PowerSeries.X := by rw [he, hl]; exact hLE
      rw [← ih, ← PowerSeries.subst_comp_subst_apply hex hb g.l, hLE', PowerSeries.subst_X hb]
    show _ = MvPowerSeries.subst (![PowerSeries.X, Formalism.L2.Th1.A.nSer g.W N] : Fin 2 → PowerSeries ℂ_[p])
      (Formalism.L2.Th1.A.fgl g.W)
    rw [← hadd]
    show _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l +
      PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l) g.ex
    rw [hN, PowerSeries.X_subst]
    congr 1
    push_cast
    rw [map_add, map_one]
    ring

/- English proof (translation)
Introduce `p _ g hOk`. Establish `hl : g.l = Formalism.L2.Th1.A.logSer g.W` using `Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1`. Establish `he : g.ex = Formalism.L2.Th1.A.expSer g.W` using `Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk`. Establish `hM` using `Formalism.L2.KerInert.Dict.intModel_of_ok hOk`. Take `⟨-, -, -, hEL, -⟩` from `Formalism.L2.Th1.A.expSpec ℂ_[p] g.W`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf n`. Establish `hJ` using `(Formalism.L2.Th1.A.jetMem ℂ_[p] g.W (Formalism.G.unitBall ℂ_[p]) hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2).2.1 f hf n`. Rewrite using `[he]`. Conclude with `hJ`.

Rewrite using `[hl, he]`. Conclude with `hEL`. Introduce `N n`. Rewrite using `[subst_mul_log_eq_nSer g hOk N, ← intModel_map g hM]`. Establish `hz` using `GlobalTheory.WeierstrassFormal.map_zsmul (intModel g hM) (Formalism.G.unitBall ℂ_[p]).subtype (N : ℤ)`.

Express the relevant statement in the definitionally equal form `PowerSeries.map _ (Formalism.L2.Th1.A.nSer _ N) = Formalism.L2.Th1.A.nSer _ N at hz`. Rewrite using `[← hz, PowerSeries.coeff_map]`. Conclude with `(PowerSeries.coeff n (Formalism.L2.Th1.A.nSer (intModel g hM) N)).2`.
-/
theorem int_dlog : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → (∀ (f : PowerSeries ℂ_[p]), (∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (PowerSeries.subst g.ex f : PowerSeries ℂ_[p])‖ ≤ 1) ∧ (PowerSeries.subst g.l g.ex : PowerSeries ℂ_[p]) = PowerSeries.X ∧ ∀ N : ℕ, ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p])‖ ≤ 1 := by
  intro p _ g hOk
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hM := Formalism.L2.KerInert.Dict.intModel_of_ok hOk
  obtain ⟨-, -, -, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  refine ⟨?_, ?_, ?_⟩
  · intro f hf n
    have hJ := (Formalism.L2.Th1.A.jetMem ℂ_[p] g.W (Formalism.G.unitBall ℂ_[p]) hM.1 hM.2.1 hM.2.2.1
      hM.2.2.2.1 hM.2.2.2.2).2.1 f hf n
    rw [he]
    exact hJ
  · rw [hl, he]
    exact hEL
  · intro N n
    rw [subst_mul_log_eq_nSer g hOk N, ← intModel_map g hM]
    have hz := GlobalTheory.WeierstrassFormal.map_zsmul (intModel g hM) (Formalism.G.unitBall ℂ_[p]).subtype (N : ℤ)
    change PowerSeries.map _ (Formalism.L2.Th1.A.nSer _ N) = Formalism.L2.Th1.A.nSer _ N at hz
    rw [← hz, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (Formalism.L2.Th1.A.nSer (intModel g hM) N)).2

end GlobalTheory.IntDLog

end
