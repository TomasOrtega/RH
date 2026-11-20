import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecGapOfFormula

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

/- English proof (translation)
Introduce `hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv`. Establish `hU` using `hDS.2.2.1`. Establish `h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖`. Take `⟨k, X, hk, hX, hgk⟩` from `(polar_decomposition_holds n ε).1 g hg`. Establish `hs'` using `GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)`.

Establish `hkk : star k * k = 1` using `hk.1.1`. Establish `e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u)`. Establish `h` using `hU.1.2 (star k) hs' g hg`. Rewrite `h` using `[show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]]`. Conclude with `congrArg (fun F : H →L[ℂ] H => F u) h`.

Set `L : H →ₗᵢ[ℂ] H` to `⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩`. Establish `e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ` using `L.inner_map_map v (σ g u)`. Establish `hb` using `dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v) (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)`. Rewrite `hb` using `[e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk]`. Conclude with `hb`.

Use `⟨h1, h1.trans ?_⟩` and prove the remaining obligations. Establish `h0 : 0 ≤ h` using `le_trans (by positivity) hh`. Take `⟨h2, h3⟩` from `dOp_facts hg`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)`.
-/
theorem decGap_of_formulaGap : FormulaGap → DecGap := by
  intro hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv
  have hU := hDS.2.2.1
  have h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ := by
    obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 g hg
    have hs' := GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)
    have hkk : star k * k = 1 := hk.1.1
    have e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u) := by
      have h := hU.1.2 (star k) hs' g hg
      rw [show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]] at h
      exact congrArg (fun F : H →L[ℂ] H => F u) h
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩
    have e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ := L.inner_map_map v (σ g u)
    have hb := dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v)
      (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)
    rw [e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk] at hb
    exact hb
  refine ⟨h1, h1.trans ?_⟩
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨h2, h3⟩ := dOp_facts hg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)

end GlobalTheory.DecGapBound
