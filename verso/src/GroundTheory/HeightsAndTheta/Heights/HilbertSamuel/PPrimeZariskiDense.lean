import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeZariskiDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Establish `hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Conclude with `hz.2 f hf`.

Conclude with `RingHom.mem_ker.mp (hle hF)`.
-/
theorem PrimeZariskiDense.eval_eq_zero_of_mem_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)

/- English proof (translation)
Introduce `K _ ι _ P j hP hj g hg z hz`. Distinguish the cases in `hrel : IsRelevant P`. Use `set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc`. Establish `hgj : g * map (Int.castRingHom ℂ) j ∈ Pc`. Use `h1 K ι P hP hrel _ fun w hw => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `hjw : eval w (map (Int.castRingHom ℂ) j) = 0`. Rewrite using `[hjw, mul_zero]`. Rewrite using `[hg w hw hjw, zero_mul]`. Establish `hrad : Pc.radical = Pc` using `(h2 (Σ k, ι k) P hP).radical`.

Establish `hgPc : g ∈ Pc`. Rewrite using `[← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]`. Introduce `Q hQ`. Express the relevant statement in the definitionally equal form `Q ∈ Pc.minimalPrimes at hQ`. Establish `hQp : Q.IsPrime` using `hQ.1.1`.

Establish `hjQ : map (Int.castRingHom ℂ) j ∉ Q`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Rewrite using `[← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]`. Conclude with `h`.

Conclude with `(hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ`. Conclude with `PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc`. It suffices to derive a contradiction. Simplify using `only [IsRelevant, not_forall, not_exists, not_not] at hrel`. Take `⟨k, hk⟩` from `hrel`.

Take `⟨i, hi⟩` from `hz.1 k`. Apply `hi` to reduce the goal to its premises. Simplify using `using hz.2 _ (hk i)`.
-/
theorem PrimeZariskiDense.proof (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
