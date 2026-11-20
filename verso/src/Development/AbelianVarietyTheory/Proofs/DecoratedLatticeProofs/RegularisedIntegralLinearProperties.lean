import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinearStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.RegAdd

/- English proof (translation)
Establish `e : sphericalEisenstein d b h = fun s => ∑' q, (fun _ => (1 : ℂ)) q * npow ((fun q => GlobalTheory.Eis.term (stab d) (GQ T) (iwAbs (absDet d) (Kmax T b)) h q) q) (s - (-(rhoH T r : ℂ)))`. Use function extensionality and compare the values at `s`. Simplify using `only [sphericalEisenstein, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]`. Rewrite using `[e]`. Use `GlobalTheory.Eis.analyticOnNhd_tsum_npow (fun _ => iwAbs_pos _ _ _) fun s hs => ?_` and prove the remaining obligations.

Use `hA.1 s hs h` as an intermediate fact. Simplify `this` using `only [GlobalTheory.Eis.CosetConv, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]`.
-/
theorem analytic_on_auxiliary_eisenstein {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D))
    (hA : EisensteinContinues d b) (h : GA D T) : AnalyticOnNhd ℂ (sphericalEisenstein d b h) (rightOf (rhoH T r)) := by
  have e : sphericalEisenstein d b h = fun s => ∑' q, (fun _ => (1 : ℂ)) q *
      npow ((fun q => GlobalTheory.Eis.term (stab d) (GQ T) (iwAbs (absDet d) (Kmax T b)) h q) q) (s - (-(rhoH T r : ℂ))) := by
    funext s
    simp only [sphericalEisenstein, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]
  rw [e]
  refine GlobalTheory.Eis.analyticOnNhd_tsum_npow (fun _ => iwAbs_pos _ _ _) fun s hs => ?_
  have := hA.1 s hs h
  simpa only [GlobalTheory.Eis.CosetConv, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add] using this

end GlobalTheory.Core.Rk.RegAdd

open GlobalTheory.Core.Rk.RegAdd in
/- English proof (translation)
Introduce `D ψ θ S W W₀ r' d₀ b' χS χ omh hθ hW mW hA τ zH P hR`. Take `⟨hadd, hsmul, -⟩` from `GlobalTheory.T.omega_centre_linear D ψ θ S W χS χ omh hθ hW τ zH`. Establish `hhol : ∀ s : ℂ, rhoH W r' < s.re → ∀ h, HolValueAt (sphericalEisenstein d₀ b' h) s (sphericalEisenstein d₀ b' h s)` using `fun s hs h => holValueAt_self (analytic_on_auxiliary_eisenstein d₀ b' hA h) hs`. Establish `hconv : ∀ φ, IsThetaFunO ψ S W φ → ∀ g (s : ℂ), rhoH W r' < s.re → ThetaPairConv omh mW (omCentreT omh θ τ zH φ) (fun h => sphericalEisenstein d₀ b' h s) g` using `fun φ hφ g s hs => (((hR φ hφ).2 g).2.2 s _ (hhol s hs)).1`. Establish `hcoef : ∀ φ, IsThetaFunO ψ S W φ → ∀ g, CoeffAt (regInt omh mW θ τ d₀ b' zH P φ g) (rhoH W r') (-1) (regRes omh mW θ τ d₀ b' zH P φ g)` using `fun φ hφ g => by`.

Take `⟨H, hH⟩` from `((hR φ hφ).2 g).1`. Conclude with `coeffAt_laurent (hH.subset_contDom (Set.mem_univ _)) _`. Use `⟨fun f f' hf hf' g => ?_, fun c f hf g => ?_⟩` and prove the remaining obligations. Establish `e : EqRight (fun s => regInt omh mW θ τ d₀ b' zH P f g s + regInt omh mW θ τ d₀ b' zH P f' g s) (regInt omh mW θ τ d₀ b' zH P (f + f') g)`. Use `⟨rhoH W r', fun s hs => ?_⟩` and prove the remaining obligations.

Simplify using `only [regInt, thetaPair, hadd f f' hf hf', MeasureTheory.average]`. Rewrite using `[← mul_add, ← MeasureTheory.integral_add (hconv f hf g s hs).to_average (hconv f' hf' g s hs).to_average]`. Use `congr 1`. Use `congrArg _ (funext fun q => ?_)` and prove the remaining obligations. Simplify using `only [AutomorphicL2Unitary.descend, thetaKO, map_add, LinearMap.add_apply, Pi.add_apply, add_mul]`.

Conclude with `(((hcoef f hf g).add (hcoef f' hf' g)).congr e).laurent_eq`. Establish `e : EqRight (fun s => c * regInt omh mW θ τ d₀ b' zH P f g s) (regInt omh mW θ τ d₀ b' zH P (c • f) g)`. Use `⟨0, fun s _ => ?_⟩` and prove the remaining obligations. Simplify using `only [regInt, thetaPair, hsmul c f hf, MeasureTheory.average]`. Rewrite using `[mul_left_comm, ← MeasureTheory.integral_const_mul]`.

Use `congr 1`. Use `congrArg _ (funext fun q => ?_)` and prove the remaining obligations. Simplify using `only [AutomorphicL2Unitary.descend, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `(((hcoef f hf g).const_mul c).congr e).laurent_eq`.
-/
theorem GlobalTheory.Core.Rk.regRes_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χS χ : (AE D)ˣ →* Circle) (omh : WRep S W), IsInfFam θ → IsWeilDatumO ψ S W χS χ omh → ∀ mW : Measure (GA D W), EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), (∀ φ', IsThetaFunO ψ S W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → (∀ f f', IsThetaFunO ψ S W f → IsThetaFunO ψ S W f' → ∀ g, regRes omh mW θ τ d₀ b' zH P (f + f') g = regRes omh mW θ τ d₀ b' zH P f g + regRes omh mW θ τ d₀ b' zH P f' g) ∧ ∀ (c : ℂ) f, IsThetaFunO ψ S W f → ∀ g, regRes omh mW θ τ d₀ b' zH P (c • f) g = c * regRes omh mW θ τ d₀ b' zH P f g := by
  intro D ψ θ S W W₀ r' d₀ b' χS χ omh hθ hW mW hA τ zH P hR
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.omega_centre_linear D ψ θ S W χS χ omh hθ hW τ zH
  have hhol : ∀ s : ℂ, rhoH W r' < s.re → ∀ h, HolValueAt (sphericalEisenstein d₀ b' h) s (sphericalEisenstein d₀ b' h s) :=
    fun s hs h => holValueAt_self (analytic_on_auxiliary_eisenstein d₀ b' hA h) hs
  have hconv : ∀ φ, IsThetaFunO ψ S W φ → ∀ g (s : ℂ), rhoH W r' < s.re →
      ThetaPairConv omh mW (omCentreT omh θ τ zH φ) (fun h => sphericalEisenstein d₀ b' h s) g :=
    fun φ hφ g s hs => (((hR φ hφ).2 g).2.2 s _ (hhol s hs)).1
  have hcoef : ∀ φ, IsThetaFunO ψ S W φ → ∀ g, CoeffAt (regInt omh mW θ τ d₀ b' zH P φ g) (rhoH W r') (-1)
      (regRes omh mW θ τ d₀ b' zH P φ g) := fun φ hφ g => by
    obtain ⟨H, hH⟩ := ((hR φ hφ).2 g).1
    exact coeffAt_laurent (hH.subset_contDom (Set.mem_univ _)) _
  refine ⟨fun f f' hf hf' g => ?_, fun c f hf g => ?_⟩
  · have e : EqRight (fun s => regInt omh mW θ τ d₀ b' zH P f g s + regInt omh mW θ τ d₀ b' zH P f' g s)
        (regInt omh mW θ τ d₀ b' zH P (f + f') g) := by
      refine ⟨rhoH W r', fun s hs => ?_⟩
      simp only [regInt, thetaPair, hadd f f' hf hf', MeasureTheory.average]
      rw [← mul_add, ← MeasureTheory.integral_add (hconv f hf g s hs).to_average (hconv f' hf' g s hs).to_average]
      congr 1
      refine congrArg _ (funext fun q => ?_)
      simp only [AutomorphicL2Unitary.descend, thetaKO, map_add, LinearMap.add_apply, Pi.add_apply, add_mul]
    exact (((hcoef f hf g).add (hcoef f' hf' g)).congr e).laurent_eq
  · have e : EqRight (fun s => c * regInt omh mW θ τ d₀ b' zH P f g s) (regInt omh mW θ τ d₀ b' zH P (c • f) g) := by
      refine ⟨0, fun s _ => ?_⟩
      simp only [regInt, thetaPair, hsmul c f hf, MeasureTheory.average]
      rw [mul_left_comm, ← MeasureTheory.integral_const_mul]
      congr 1
      refine congrArg _ (funext fun q => ?_)
      simp only [AutomorphicL2Unitary.descend, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact (((hcoef f hf g).const_mul c).congr e).laurent_eq
