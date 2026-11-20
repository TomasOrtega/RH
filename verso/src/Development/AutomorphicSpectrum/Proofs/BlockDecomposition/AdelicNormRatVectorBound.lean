import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.MajHeight

/- English proof (translation)
Establish `h0` using `norm_nonneg (y 0)`. Establish `h1` using `norm_nonneg (y 1)`. Establish `h2` using `norm_nonneg (y 2)`. Rewrite using `[Reduction.euclidNorm, Fin.sum_univ_three, Fin.sum_univ_three]`. Use `Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩` and prove the remaining obligations.

Use polynomial arithmetic with `[mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]`.
-/
theorem euclidNorm_le_sum {E : Type*} [NormedField E] (y : Fin 3 → E) :
    Reduction.euclidNorm y ≤ ∑ i, ‖y i‖ := by
  have h0 := norm_nonneg (y 0)
  have h1 := norm_nonneg (y 1)
  have h2 := norm_nonneg (y 2)
  rw [Reduction.euclidNorm, Fin.sum_univ_three, Fin.sum_univ_three]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

/- English proof (translation)
Rewrite using `[Fintype.prod_unique, InfinitePlace.mult_isReal ⟨_, RationalIdeles.isReal_infinitePlace default⟩, pow_one]`. Use `(euclidNorm_le_sum _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Reduction.infComp_ratVec]`. Express the relevant statement in the definitionally equal form `‖algebraMap ℚ (default : InfinitePlace ℚ).Completion (y i)‖ = _`.

Rewrite using `[eq_ratCast, InfinitePlace.Completion.Rat.norm_infinitePlace_completion]`. Simplify using the standard rewrite rules.
-/
theorem infPart_le (y : Fin 3 → ℚ) :
    ∏ w : InfinitePlace ℚ, Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec y)) ^ w.mult
      ≤ ∑ i, |((y i : ℚ) : ℝ)| := by
  rw [Fintype.prod_unique,
    InfinitePlace.mult_isReal ⟨_, RationalIdeles.isReal_infinitePlace default⟩, pow_one]
  refine (euclidNorm_le_sum _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Reduction.infComp_ratVec]
  change ‖algebraMap ℚ (default : InfinitePlace ℚ).Completion (y i)‖ = _
  rw [eq_ratCast, InfinitePlace.Completion.Rat.norm_infinitePlace_completion]
  simp

/- English proof (translation)
Use `Reduction.norm_le_one_of_mem v ?_` and prove the remaining obligations. Rewrite using `[Reduction.finComp_ratVec]`. Use `(coe_mem_adicCompletionIntegers_iff v (k : ℚ)).2 ?_` and prove the remaining obligations. Establish `h : (k : ℚ) = algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ)` using `by simp`. Rewrite using `[h]`.

Conclude with `HeightOneSpectrum.valuation_le_one v _`.
-/
theorem norm_intCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    ‖Reduction.finComp v (Reduction.ratVec (fun _ : Fin 1 => (k : ℚ))) 0‖ ≤ 1 := by
  refine Reduction.norm_le_one_of_mem v ?_
  rw [Reduction.finComp_ratVec]
  refine (coe_mem_adicCompletionIntegers_iff v (k : ℚ)).2 ?_
  have h : (k : ℚ) = algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ) := by simp
  rw [h]
  exact HeightOneSpectrum.valuation_le_one v _

/- English proof (translation)
Use `finprod_induction (f := fun v : HeightOneSpectrum (𝓞 ℚ) => ‖Reduction.finComp v (Reduction.ratVec y)‖) (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩ (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩) (fun v => ⟨norm_nonneg _, (pi_norm_le_iff_of_nonneg zero …` as an intermediate fact. Take `⟨k, hk⟩` from `hy i`. Establish `h` using `norm_intCast_le_one v k`. Rewrite `h` using `[Reduction.finComp_ratVec]`. Rewrite using `[Reduction.finComp_ratVec, hk]`.

Conclude with `h⟩)`. Conclude with `this.2`.
-/
theorem finPart_le_one (y : Fin 3 → ℚ) (hy : ∀ i, ∃ k : ℤ, y i = k) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖Reduction.finComp v (Reduction.ratVec y)‖ ≤ 1 := by
  have := finprod_induction (f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
      ‖Reduction.finComp v (Reduction.ratVec y)‖) (fun x : ℝ => 0 ≤ x ∧ x ≤ 1)
    ⟨zero_le_one, le_rfl⟩
    (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
    (fun v => ⟨norm_nonneg _, (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      obtain ⟨k, hk⟩ := hy i
      have h := norm_intCast_le_one v k
      rw [Reduction.finComp_ratVec] at h
      rw [Reduction.finComp_ratVec, hk]
      exact h⟩)
  exact this.2

/- English proof (translation)
Introduce `M hM z hz`. Distinguish the cases in `h0 : z = 0`. Substitute `h0` using the available equality. Establish `h` using `infPart_le (0 : Fin 3 → ℚ)`. Establish `hnn : 0 ≤ ∏ w : InfinitePlace ℚ, Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult` using `Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _`.

Establish `hz0 : ∏ w : InfinitePlace ℚ, Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult = 0` using `le_antisymm (by simpa using h) hnn`. Rewrite using `[Reduction.adelicNorm, hz0, zero_mul]`. Simplify using the standard rewrite rules. Establish `hc : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hscale : Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) = Reduction.adelicNorm (Reduction.ratVec ((M : ℚ) • z) : Fin 3 → 𝔸[ℚ])`.

Rewrite using `[Reduction.ratVec_smul, Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec h0) hc]`. Rewrite using `[hscale, Reduction.adelicNorm]`. Establish `hinf` using `infPart_le ((M : ℚ) • z)`. Establish `hfin` using `finPart_le_one ((M : ℚ) • z) (fun i => by simpa using hz i)`. Establish `hsum : ∑ i, |((((M : ℚ) • z) i : ℚ) : ℝ)| = M * ∑ i, |((z i : ℚ) : ℝ)|`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[abs_mul]`. Rewrite using `[← hsum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem adelicNorm_ratVec_le : ∀ M : ℕ, 0 < M → ∀ z : Fin 3 → ℚ,
    (∀ i, ∃ k : ℤ, (M : ℚ) * z i = k) →
    Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) ≤ M * ∑ i, |((z i : ℚ) : ℝ)| := by
  intro M hM z hz
  by_cases h0 : z = 0
  · subst h0
    have h := infPart_le (0 : Fin 3 → ℚ)
    have hnn : 0 ≤ ∏ w : InfinitePlace ℚ,
        Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _
    have hz0 : ∏ w : InfinitePlace ℚ,
        Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult = 0 :=
      le_antisymm (by simpa using h) hnn
    rw [Reduction.adelicNorm, hz0, zero_mul]
    simp
  · have hc : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hscale : Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) =
        Reduction.adelicNorm (Reduction.ratVec ((M : ℚ) • z) : Fin 3 → 𝔸[ℚ]) := by
      rw [Reduction.ratVec_smul, Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec h0) hc]
    rw [hscale, Reduction.adelicNorm]
    have hinf := infPart_le ((M : ℚ) • z)
    have hfin := finPart_le_one ((M : ℚ) • z) (fun i => by simpa using hz i)
    have hsum : ∑ i, |((((M : ℚ) • z) i : ℚ) : ℝ)| = M * ∑ i, |((z i : ℚ) : ℝ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [abs_mul]
    rw [← hsum]
    calc _ ≤ (∑ i, |((((M : ℚ) • z) i : ℚ) : ℝ)|) * 1 :=
          mul_le_mul hinf hfin (finprod_nonneg fun _ => norm_nonneg _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = _ := mul_one _

end GlobalTheory.CompanionTheory.MajHeight
