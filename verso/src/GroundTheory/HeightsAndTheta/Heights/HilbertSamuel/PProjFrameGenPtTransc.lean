import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGenPtTransc

open ProjFrameFibrePt

/- English proof (translation)
Introduce `D Ω _ _ κ _ x e _hA hF G`. Use `coordIdeal_isPrime ℤ x` as an intermediate fact. Rewrite using `[transcendental_iff]`. Introduce `q hq`. Establish `hc : ∀ n, ∃ g : MvPolynomial (Ix κ) ℤ, aeval (fun p : Ix κ => G.x' (aV D p.2)) g = ((q.coeff n : _) : G.Φ')`.

Introduce `n`. Establish `h : ((q.coeff n : _) : G.Φ') ∈ (aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) : MvPolynomial (Ix κ) ℤ →ₐ[ℤ] G.Φ').range`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`. Conclude with `(q.coeff n).2`. Take `⟨g, hg⟩` from `h`.

Conclude with `⟨g, hg⟩`. Use `choose g hg using hc`. Establish `hFΓ : (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) ∈ graphP x e`. Establish `key : ∀ F, aeval G.x' F = 0 → F ∈ graphP x e` using `fun F h => by`. Rewrite using `[graphP, ← G.genericFibre_ker_target, RingHom.mem_ker]`.

Conclude with `h`. Use `key _ ?_` and prove the remaining obligations. Rewrite `hq` using `[Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]`. Rewrite using `[← hq, map_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, aeval_X, aeval_rename]`. Conclude with `congrArg (· * _) (hg n)`. Use `replace hFΓ : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e)) (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) = 0 := hFΓ`. Rewrite `hFΓ` using `[map_sum]`. Simplify using `only [map_mul, map_pow, graphMap_rename_inl, graphMap_inr, ProjFrameGraph.linForm_projMat] at hFΓ`.

Simplify using `only [mul_pow, ← mul_assoc, ← C_pow, ← C_mul] at hFΓ`. Establish `hX : Ideal.Quotient.mk (coordIdeal ℤ x) (X (e 0)) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem, X_mem_coordIdeal_iff]`. Conclude with `ProjFrameGraph.frame_ne_zero hF 0`. Establish `hcoef : ∀ m, q.coeff m = 0`.

Introduce `m`. Distinguish the cases in `hm : m ∈ q.support`. Establish `h1` using `congrArg (coeff (Finsupp.single () m)) hFΓ`. Rewrite `h1` using `[coeff_sum, coeff_zero, Finset.sum_eq_single m]`. Rewrite `h1` using `[coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]`.

Establish `h2` using `(mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hX)`. Rewrite `h2` using `[Ideal.Quotient.eq_zero_iff_mem]`. Establish `h3` using `aeval_inl_eq_zero G h2`. Rewrite `h3` using `[hg m]`. Conclude with `Subtype.ext h3`.

Introduce `n _ hn`. Rewrite using `[coeff_C_mul, coeff_X_pow, if_neg, mul_zero]`. Introduce `h`. Conclude with `hn (Finsupp.single_injective () h)`. Introduce `h`.

Conclude with `absurd hm h`. Conclude with `Polynomial.notMem_support_iff.1 hm`. Conclude with `Polynomial.ext fun m => by rw [hcoef m, Polynomial.coeff_zero]`.
-/
theorem proof : ProjFrameGenPtTransc.Statement := by
  intro D Ω _ _ κ _ x e _hA hF G
  classical
  have := coordIdeal_isPrime ℤ x
  rw [transcendental_iff]
  intro q hq
  have hc : ∀ n, ∃ g : MvPolynomial (Ix κ) ℤ,
      aeval (fun p : Ix κ => G.x' (aV D p.2)) g = ((q.coeff n : _) : G.Φ') := by
    intro n
    have h : ((q.coeff n : _) : G.Φ') ∈
        (aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) : MvPolynomial (Ix κ) ℤ →ₐ[ℤ] G.Φ').range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff n).2
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg⟩
  choose g hg using hc
  have hFΓ : (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) ∈ graphP x e := by
    have key : ∀ F, aeval G.x' F = 0 → F ∈ graphP x e := fun F h => by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker]; exact h
    refine key _ ?_
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hq
    rw [← hq, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, aeval_X, aeval_rename]
    exact congrArg (· * _) (hg n)
  replace hFΓ : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) = 0 := hFΓ
  rw [map_sum] at hFΓ
  simp only [map_mul, map_pow, graphMap_rename_inl, graphMap_inr, ProjFrameGraph.linForm_projMat] at hFΓ
  simp only [mul_pow, ← mul_assoc, ← C_pow, ← C_mul] at hFΓ
  have hX : Ideal.Quotient.mk (coordIdeal ℤ x) (X (e 0)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, X_mem_coordIdeal_iff]
    exact ProjFrameGraph.frame_ne_zero hF 0
  have hcoef : ∀ m, q.coeff m = 0 := by
    intro m
    by_cases hm : m ∈ q.support
    · have h1 := congrArg (coeff (Finsupp.single () m)) hFΓ
      rw [coeff_sum, coeff_zero, Finset.sum_eq_single m] at h1
      · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one] at h1
        have h2 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hX)
        rw [Ideal.Quotient.eq_zero_iff_mem] at h2
        have h3 := aeval_inl_eq_zero G h2
        rw [hg m] at h3
        exact Subtype.ext h3
      · intro n _ hn
        rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
        intro h
        exact hn (Finsupp.single_injective () h)
      · intro h
        exact absurd hm h
    · exact Polynomial.notMem_support_iff.1 hm
  exact Polynomial.ext fun m => by rw [hcoef m, Polynomial.coeff_zero]

end ProjFrameGenPtTransc

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
