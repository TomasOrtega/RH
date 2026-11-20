import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientDerivativeBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomMass

/- English proof (translation)
Establish `hn : ‖((Real.sqrt d : ℝ) : ℂ) • v‖ = Real.sqrt d * ‖v‖`. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)]`. Establish `hc : ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) = ENNReal.ofReal (Real.sqrt d * ‖v‖)`. Rewrite using `[← hn, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]`. Rewrite using `[hc, ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg d) (norm_nonneg v)), mul_pow, Real.sq_sqrt hd, one_mul]`.
-/
theorem integrand_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {d : ℝ} (hd : 0 ≤ d) (v : Wp) :
    ENNReal.ofReal (1 * (d * ‖v‖ ^ 2)) = ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) ^ 2 := by
  have hn : ‖((Real.sqrt d : ℝ) : ℂ) • v‖ = Real.sqrt d * ‖v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)]
  have hc : ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) = ENNReal.ofReal (Real.sqrt d * ‖v‖) := by
    rw [← hn, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  rw [hc, ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg d) (norm_nonneg v)), mul_pow,
    Real.sq_sqrt hd, one_mul]

/- English proof (translation)
Introduce `hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν`. Take `⟨hNum, hFam, hSide, hSF⟩` from `hS`. Take `⟨hBeL, hdg, hfd⟩` from `hSF ν hν`. Establish `hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))` using `hFam ν hν`. Take `⟨_, _, _, _, _, _, _, _, _, _, hGap0, hGapOK, _, hq0h, _⟩` from `hNum`.

Establish `hνa : ∀ a, |(ν a : ℝ)| ≤ (q0 : ℝ)`. Introduce `a`. Establish `h1 : (ν a).natAbs ≤ BranchingSupport.n1 ν` using `Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)`. Establish `h2 : ((ν a).natAbs : ℝ) ≤ (q0 : ℝ)` using `by exact_mod_cast h1.trans hν`. Establish `h3 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ)` using `by rw [Nat.cast_natAbs, Int.cast_abs]`.

Rewrite using `[h3]`. Conclude with `h2`. Establish `hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 4)`. Introduce `a c hac`. Establish `h0` using `hGap0 a c hac`.

Take `⟨ha1, ha2⟩` from `abs_le.mp (hνa a)`. Take `⟨hc1, hc2⟩` from `abs_le.mp (hνa c)`. Establish `hd : |(ν c : ℝ) - ν a| ≤ 2 * (q0 : ℝ)` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Establish `hx` using `abs_sub_abs_le_abs_sub (lam a - lam c) ((ν c : ℝ) - ν a)`. Establish `e : (lam a - lam c) - ((ν c : ℝ) - ν a) = (lam a + ν a) - (lam c + ν c)` using `by ring`.

Rewrite `hx` using `[e]`. Establish `hq : (0 : ℝ) ≤ q0` using `Nat.cast_nonneg q0`. Use `show h / 4 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hIso : BranchingSupport.NzOn (R ν) (l ν) → BranchingSupport.IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w)` using `fun hNz => Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 4) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDG hgap hGapOK hSide hBeL hfd hNz`.

Establish `hEq : BranchingSupport.NzOn (R ν) (l ν) → ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)`. Introduce `hNz w hw`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun w hw => ?_, fun hNz => ⟨hIso hNz, hEq hNz⟩⟩` and prove the remaining obligations. Distinguish the cases in `hNz : BranchingSupport.NzOn (R ν) (l ν)`.

Conclude with `(hEq hNz w hw).le`. Establish `hz : ∀ v ∈ (R ν).sm, l ν v = 0`. Introduce `v hv`. Assume the negation of the conclusion as `hne`. Conclude with `hNz ⟨v, hv, hne⟩`.

Take `⟨_, _, _, _, hW, hN, hG, hQ⟩` from `hSide`. Take `⟨hmS, hmS0⟩` from `Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN`. Establish `hae` using `Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hmS hmS0 hQ`. Establish `hKF : PI.KFinSmooth` using `hH.1.2.2.1`. Establish `hinv` using `(Gp91.GlobalTheory.rep_basic_of_isDS hKF k r _ _ (R ν) hDG).2.2.2.1`.

Establish `h0 : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0]`. Conclude with `zero_le`.
-/
theorem mom_mass : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  obtain ⟨hBeL, hdg, hfd⟩ := hSF ν hν
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := hFam ν hν
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hGap0, hGapOK, _, hq0h, _⟩ := hNum
  have hνa : ∀ a, |(ν a : ℝ)| ≤ (q0 : ℝ) := by
    intro a
    have h1 : (ν a).natAbs ≤ BranchingSupport.n1 ν :=
      Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
    have h2 : ((ν a).natAbs : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast h1.trans hν
    have h3 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h3]
    exact h2
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 4) := by
    intro a c hac
    have h0 := hGap0 a c hac
    obtain ⟨ha1, ha2⟩ := abs_le.mp (hνa a)
    obtain ⟨hc1, hc2⟩ := abs_le.mp (hνa c)
    have hd : |(ν c : ℝ) - ν a| ≤ 2 * (q0 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    have hx := abs_sub_abs_le_abs_sub (lam a - lam c) ((ν c : ℝ) - ν a)
    have e : (lam a - lam c) - ((ν c : ℝ) - ν a) = (lam a + ν a) - (lam c + ν c) := by ring
    rw [e] at hx
    have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg q0
    show h / 4 ≤ |(lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ))|
    linarith
  have hIso : BranchingSupport.NzOn (R ν) (l ν) →
      BranchingSupport.IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) := fun hNz =>
    Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 4) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDG hgap hGapOK hSide hBeL
      hfd hNz
  have hEq : BranchingSupport.NzOn (R ν) (l ν) → ∀ w ∈ (R ν).sm,
      ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2) := by
    intro hNz w hw
    calc ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
        = ∫⁻ x, ((‖((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν ((R ν).σ (Matrix.of x) w)‖₊ : ENNReal)) ^ 2 ∂νq :=
          MeasureTheory.lintegral_congr (fun x => integrand_eq hdg.le _)
      _ = ENNReal.ofReal (‖w‖ ^ 2) := (hIso hNz).2 w hw
  refine ⟨fun w hw => ?_, fun hNz => ⟨hIso hNz, hEq hNz⟩⟩
  by_cases hNz : BranchingSupport.NzOn (R ν) (l ν)
  · exact (hEq hNz w hw).le
  · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
      intro v hv
      by_contra hne
      exact hNz ⟨v, hv, hne⟩
    obtain ⟨_, _, _, _, hW, hN, hG, hQ⟩ := hSide
    obtain ⟨hmS, hmS0⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hmS hmS0 hQ
    have hKF : PI.KFinSmooth := hH.1.2.2.1
    have hinv := (Gp91.GlobalTheory.rep_basic_of_isDS hKF k r _ _ (R ν) hDG).2.2.2.1
    have h0 : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      calc ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
          = ∫⁻ _x, (0 : ENNReal) ∂νq :=
            MeasureTheory.lintegral_congr_ae (hae.mono fun x hx => by simp [hz _ (hinv _ hx w hw)])
        _ = 0 := MeasureTheory.lintegral_zero
    rw [h0]
    exact zero_le

end GlobalTheory.MomMass
