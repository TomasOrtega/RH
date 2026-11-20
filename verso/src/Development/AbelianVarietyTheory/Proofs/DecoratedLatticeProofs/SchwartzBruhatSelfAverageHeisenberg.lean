import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)

noncomputable section
namespace GlobalTheory.PosOne

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ hψ1 ν hν μ hμ' Φ`. Use `hν.1` as an intermediate fact. Use `secondCountable k` as an intermediate fact. Use `t2Space k` as an intermediate fact. Establish `hF` using `GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν`.

Establish `main : ∀ Φ₀ : SB (n' → k), ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = w.1 ∧ (∀ h, opE ψ ν p (om μ 1 h w.1) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧ ∀ L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + …`. Introduce `Φ₀`. Establish `hh` using `hF.1 Φ₀`. Set `T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)` to `fun u => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) p u, 1) Φ`. Establish `hT : IsLocallyConstant T` using `(hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2`.

Take `⟨w, hw⟩` from `GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k) (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by`. Simplify using `only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]`. Use `⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, fun L => ?_⟩` and prove the remaining obligations. Use `(hw ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))).trans ?_` and prove the remaining obligations. Rewrite using `[opEFJ]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Simplify using `only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]`. Use `congr 1`. Use `GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c p hp1 hpc ψ hψ ν μ (omR μ (1, h) Φ) u x₀` as an intermediate fact.

Rewrite `this` using `[← omR_val, omR_mul, one_mul, mul_one]`. Rewrite using `[omR_mul, one_mul, mul_one]`. Conclude with `this`. Rewrite using `[hw L]`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Simplify using `only [T, map_smul, smul_eq_mul]`. Use `⟨?_, fun Φ₀ => ?_⟩` and prove the remaining obligations. Establish `hU : {u : n' → k | omR μ (rowE (c + 1) p u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k)` using `((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by`. Express the relevant statement in the definitionally equal form `omR μ (rowE (c + 1) p 0, 1) Φ = Φ`.

Rewrite using `[ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])`. Take `⟨g, a, a1⟩` from `GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU`. Take `⟨Φ₀, h0⟩` from `hF.2 g`. Use `⟨Φ₀, funext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg, h0, GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]`.

Introduce `u hu`. Conclude with `congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu`. Take `⟨w, e1, e2, e3⟩` from `main Φ₀`. Use `⟨e1 ▸ w.2, fun h => e1 ▸ e2 h, fun ρ' hρ' L => ?_⟩` and prove the remaining obligations. Rewrite using `[e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e3 L]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Use `congr 2`. Conclude with `Subtype.ext ((hρ' _ Φ).trans (omR_val μ _ 1 Φ).symm).symm`.
-/
theorem avg_self_and_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∃ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = Φ.1) ∧ ∀ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∧ (∀ h, opE ψ ν p (om μ 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1)) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧ ∀ (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ), app L (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1) = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (ρ' (rowE (c + 1) p u) Φ) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ hψ1 ν hν μ hμ' Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ Φ₀ : SB (n' → k),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = w.1 ∧
      (∀ h, opE ψ ν p (om μ 1 h w.1) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧
      ∀ L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ,
        L w = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν) := by
    intro Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) p u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, fun L => ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c p hp1 hpc ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hw L]
      congr 1; funext u
      simp only [T, map_smul, smul_eq_mul]
  refine ⟨?_, fun Φ₀ => ?_⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) p u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) p 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    refine ⟨Φ₀, funext fun x => ?_⟩
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg, h0, GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
    intro u hu
    exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
  · obtain ⟨w, e1, e2, e3⟩ := main Φ₀
    refine ⟨e1 ▸ w.2, fun h => e1 ▸ e2 h, fun ρ' hρ' L => ?_⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e3 L]
    congr 1; funext u
    congr 2
    exact Subtype.ext ((hρ' _ Φ).trans (omR_val μ _ 1 Φ).symm).symm

end GlobalTheory.PosOne
