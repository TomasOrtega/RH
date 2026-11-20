import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk A _ s ι TB`. Take `⟨h0, h1, -, -⟩` from `GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s`. Use `⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `y hy`.

Establish `hn` using `(GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y`. Rewrite `hn` using `[mul_comm, hy, norm_zero]`. Establish `hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree` using `pow_pos (by exact_mod_cast h0) _`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')`. Establish `hH : IsHausdorff bk.J bk.S` using `bk.complete.toIsHausdorff`.

Establish `hF` using `GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH`. Establish `hW : ((l : ℕ) : Wq l bk.a) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (fun w : Wq l bk.a => w.coeff 1) h`. Simplify using `only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2`.

Conclude with `one_ne_zero h2`. Establish `hS : ((l : ℕ) : bk.S) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (PowerSeries.constantCoeff) h`. Rewrite `h2` using `[map_natCast, map_zero]`.

Conclude with `hW h2`. Use `hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Introduce `F hF`. Take `⟨_, -, -, -, -, -, -, -, hnorm⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h` using `hnorm x`. Rewrite `h` using `[hx, norm_zero]`. Conclude with `norm_eq_zero.1 h.symm`.
-/
theorem topBasis_disc_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap s F → Function.Injective F := by
  intro l _ K bk A _ s ι TB
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s
  refine ⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hn := (GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y
    rw [mul_comm, hy, norm_zero] at hn
    have hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast h0) _
    exact norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')
  · have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
    have hF := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
    have hW : ((l : ℕ) : Wq l bk.a) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : Wq l bk.a => w.coeff 1) h
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2
      exact one_ne_zero h2
    have hS : ((l : ℕ) : bk.S) ≠ 0 := by
      intro h
      have h2 := congrArg (PowerSeries.constantCoeff) h
      rw [map_natCast, map_zero] at h2
      exact hW h2
    have := hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)
    rwa [map_natCast] at this
  · intro F hF
    obtain ⟨_, -, -, -, -, -, -, -, hnorm⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hnorm x
    rw [hx, norm_zero] at h
    exact norm_eq_zero.1 h.symm

end GlobalTheory.BSP
