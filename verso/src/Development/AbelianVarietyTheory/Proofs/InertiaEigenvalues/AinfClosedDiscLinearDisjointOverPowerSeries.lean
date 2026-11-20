import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hl1 : (1 : ℝ≥0) < (l : ℝ≥0)` using `by exact_mod_cast hl.out.one_lt`. Establish `he : (0 : ℝ) < (bk.Ep.natDegree : ℝ)` using `by exact_mod_cast bk.deg_pos`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `BK.ρ₀`. Conclude with `NNReal.rpow_pos (by positivity)`.

Unfold `BK.ρ₀`. Conclude with `NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by`. Establish `: (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ)` using `by positivity`. Use the proof step `linarith)`.
-/
theorem breuilKisinDatum_uniformizer_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨?_, ?_⟩
  · unfold BK.ρ₀
    exact NNReal.rpow_pos (by positivity)
  · unfold BK.ρ₀
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
      have : (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith)

/- English proof (translation)
Take `⟨hρ0, hρ1⟩` from `breuilKisinDatum_uniformizer_radius_pos_lt_one bk`. Take `⟨cD, hc1, hc2, -⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj`. Use `haveI : IsAdicComplete bk.J bk.S := bk.complete`. Establish `hH : IsHausdorff bk.J bk.S` using `inferInstance`. Take `⟨hz, -⟩` from `GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH`.

Establish `hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀)` using `(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1`. Establish `hmul` using `GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk bk.ρ₀ hρ0 hρ1`. Establish `key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)`. Introduce `i`. Establish `e` using `congrArg (cD i) h`.

Rewrite `e` using `[mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1]`. Conclude with `e`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hy (hz y hc)`. Use `⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `hz` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[map_sub, TB.c_mul, TB.c_mul]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Establish `h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0`. Rewrite using `[map_sub, map_mul, map_mul, mul_sub]`.

Establish `e1` using `key i`. Establish `e2` using `key i₀`. Take the linear combination `(toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2`. Establish `hn` using `congrArg norm h0`. Rewrite `hn` using `[hmul, norm_zero, mul_eq_zero]`.

Break down `hn with hn | hn` into its components or cases. Conclude with `absurd (norm_eq_zero.1 hn) hg`. Conclude with `norm_eq_zero.1 hn`.
-/
theorem linDisjoint_disc (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀)
    (hj : IsDiscMap sA j) (x y : A) (f g : bk.DS bk.ρ₀) (hg : g ≠ 0) (hy : y ≠ 0)
    (h : toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f) :
    ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_uniformizer_radius_pos_lt_one bk
  obtain ⟨cD, hc1, hc2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hH : IsHausdorff bk.J bk.S := inferInstance
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH
  have hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) :=
    (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1
  have hmul := GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk bk.ρ₀ hρ0 hρ1

  have key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y) := by
    intro i
    have e := congrArg (cD i) h
    rw [mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (hz y hc)
  refine ⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩
  rw [← sub_eq_zero]
  apply hz
  intro i
  rw [map_sub, TB.c_mul, TB.c_mul]
  apply hinj
  rw [map_zero]
  have h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0 := by
    rw [map_sub, map_mul, map_mul, mul_sub]
    have e1 := key i
    have e2 := key i₀
    linear_combination (toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2
  have hn := congrArg norm h0
  rw [hmul, norm_zero, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact absurd (norm_eq_zero.1 hn) hg
  · exact norm_eq_zero.1 hn

end GlobalTheory.BSP
