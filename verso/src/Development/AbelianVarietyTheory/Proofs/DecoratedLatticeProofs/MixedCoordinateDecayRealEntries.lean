import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSumStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

/- English proof (translation)
Introduce `D ψ hψ θ hθ S S₀ T ρ d v N`. Take `⟨k, τs, zs, K, hK⟩` from `GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum D θ T ρ`. Use `choose Z hZ using fun i => GlobalTheory.T.dualDirection_derivative_mixedCoordinate_bound D ψ hψ θ hθ S S₀ T ρ d v (τs i) (zs i)`. Establish `hsf` using `GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T`. Use `choose Cd hCd using fun i => (hsf.2.1 (τs i) (Z i)).2`.

Proceed by induction on `N with`. Consider the case `zero`. Use `⟨1, fun f hf x w => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]`. Establish `hs : supSob ψ θ 0 f = ⨆ w, ‖f w‖ₑ` using `GlobalTheory.Size.wordSum_zero _ _ _`.

Rewrite using `[hs]`. Unfold `HypDec.mixS`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[d.integrandS_eq, enorm_mul]`. Establish `h1 : ‖ψ (symplOH S T (d.extY T a) (d.extX T x))‖ₑ = 1`.

Rewrite using `[← ofReal_norm_eq_enorm, hψ.1.2.1, ENNReal.ofReal_one]`. Rewrite using `[h1, one_mul]`. Conclude with `le_iSup (fun w => ‖f w‖ₑ) _`. Use `_ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]`. Consider the case `succ N ih`.

Take `⟨C, hC⟩` from `ih`. Use `⟨C + K.toNNReal * ∑ i, C * Cd i, fun f hf x w => ?_⟩` and prove the remaining obligations. Use `set R := realSize θ x with hRdef`. Establish `hR0 : 0 ≤ R` using `realSize_nonneg θ x`. Use `set M := d.mixS T ψ v.μ v.𝓕 f x w`.

Use `set s := supSob ψ θ (N + 1) f`. Establish `hNs : supSob ψ θ N f ≤ s` using `GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f`. Establish `hpow : ENNReal.ofReal ((1 + R) ^ (N + 1)) = ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * ENNReal.ofReal ((1 + R) ^ N)`. Rewrite using `[← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hA : ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) ≤ C * s` using `(hC f hf x w).trans (by gcongr)`. Establish `hRle : ENNReal.ofReal R ≤ K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|`. Use `(ENNReal.ofReal_le_ofReal (hK x)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => abs_nonneg _), ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]`.

Both sides reduce to the same expression. Establish `hi : ∀ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) ≤ C * Cd i * s` using `fun i => by`. Establish `hDf` using `GlobalTheory.OrientedHeis.theta_dRho hθ hψ (τs i) (Z i) hf`. Rewrite using `[← mul_assoc, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (abs_nonneg _)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ofReal_norm_eq_enorm]`. Conclude with `ENNReal.ofReal_le_ofReal (hZ i f hf x w)`. Use `_ ≤ C * supSob ψ θ N (dRho (heisO ψ S T) θ (τs i) (Z i) f) := hC _ hDf x w`. Use `_ ≤ C * (Cd i * s) := by gcongr; exact hCd i N f hf`. Use `_ = C * Cd i * s := (mul_assoc _ _ _).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpow, mul_add, mul_left_comm]`. Use `_ ≤ C * s + (K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|) * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) := add_le_add hA (by gcongr)`. Use `_ ≤ C * s + K.toNNReal * ∑ i, (C * Cd i * s : ℝ≥0∞) := by`. Rewrite using `[mul_assoc, Finset.sum_mul]`.

Conclude with `add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le)`. Use `_ = _ := by`. Use `push_cast`. Rewrite using `[add_mul, mul_assoc, Finset.sum_mul]`.
-/
theorem mixS_decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (N : ℕ), ∃ C : ℝ≥0, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v N
  obtain ⟨k, τs, zs, K, hK⟩ := GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum D θ T ρ
  choose Z hZ using fun i => GlobalTheory.T.dualDirection_derivative_mixedCoordinate_bound D ψ hψ θ hθ S S₀ T ρ d v (τs i) (zs i)
  have hsf := GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T
  choose Cd hCd using fun i => (hsf.2.1 (τs i) (Z i)).2
  induction N with
  | zero =>
    refine ⟨1, fun f hf x w => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    have hs : supSob ψ θ 0 f = ⨆ w, ‖f w‖ₑ := GlobalTheory.Size.wordSum_zero _ _ _
    rw [hs]
    unfold HypDec.mixS
    calc _ ≤ ∫⁻ a in v.𝓕, ‖heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0‖ₑ ∂v.μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ _ in v.𝓕, (⨆ w, ‖f w‖ₑ) ∂v.μ := lintegral_mono fun a => by
          rw [d.integrandS_eq, enorm_mul]
          have h1 : ‖ψ (symplOH S T (d.extY T a) (d.extX T x))‖ₑ = 1 := by
            rw [← ofReal_norm_eq_enorm, hψ.1.2.1, ENNReal.ofReal_one]
          rw [h1, one_mul]
          exact le_iSup (fun w => ‖f w‖ₑ) _
      _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + K.toNNReal * ∑ i, C * Cd i, fun f hf x w => ?_⟩
    set R := realSize θ x with hRdef
    have hR0 : 0 ≤ R := realSize_nonneg θ x
    set M := d.mixS T ψ v.μ v.𝓕 f x w
    set s := supSob ψ θ (N + 1) f
    have hNs : supSob ψ θ N f ≤ s := GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f
    have hpow : ENNReal.ofReal ((1 + R) ^ (N + 1)) =
        ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * ENNReal.ofReal ((1 + R) ^ N) := by
      rw [← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hA : ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) ≤ C * s := (hC f hf x w).trans (by gcongr)
    have hRle : ENNReal.ofReal R ≤ K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
      refine (ENNReal.ofReal_le_ofReal (hK x)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
      rfl
    have hi : ∀ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) ≤
        C * Cd i * s := fun i => by
      have hDf := GlobalTheory.OrientedHeis.theta_dRho hθ hψ (τs i) (Z i) hf
      rw [← mul_assoc, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (abs_nonneg _)]
      calc _ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ (τs i) (Z i) f) x w‖ₑ * ENNReal.ofReal ((1 + R) ^ N) := by
            gcongr
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hZ i f hf x w)
        _ ≤ C * supSob ψ θ N (dRho (heisO ψ S T) θ (τs i) (Z i) f) := hC _ hDf x w
        _ ≤ C * (Cd i * s) := by gcongr; exact hCd i N f hf
        _ = C * Cd i * s := (mul_assoc _ _ _).symm
    calc ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ (N + 1))
        = ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) := by
          rw [hpow, mul_add, mul_left_comm]
      _ ≤ C * s + (K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
            ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|) * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) :=
          add_le_add hA (by gcongr)
      _ ≤ C * s + K.toNNReal * ∑ i, (C * Cd i * s : ℝ≥0∞) := by
          rw [mul_assoc, Finset.sum_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le)
      _ = _ := by
          push_cast
          rw [add_mul, mul_assoc, Finset.sum_mul]

end GlobalTheory.Unf

end
