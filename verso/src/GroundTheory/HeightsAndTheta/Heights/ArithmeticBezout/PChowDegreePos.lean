import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `n k δ W g hk hW hg hδ`. Assume the negation of the conclusion as `hlt`. Establish `hδ0 : δ = 0` using `by omega`. Substitute `hδ0` using the available equality. Establish `hnt : NonTorsionWeight (groupWeight k n)`.

Introduce `m ij h`. Use `congrFun h ij.1` as an intermediate fact. Simplify `this` using `[groupWeight]`. Establish `hsupp : ∀ m ∈ g.support, m = 0`. Introduce `m hm`.

Establish `h1 : Finsupp.weight (groupWeight k n) m = 0` using `hδ (mem_support_iff.1 hm)`. Use extensionality with `ij`. Conclude with `(weightedDegree_eq_zero_iff hnt).1 h1 ij`. Choose the witnesses or unpack the hypotheses as in `⟨c, rfl⟩ : ∃ c, g = C c := by`. Use `⟨coeff 0 g, ?_⟩` and prove the remaining obligations.

Use extensionality with `m`. Rewrite using `[coeff_C]`. Use `split_ifs with hm`. Rewrite using `[hm]`. Assume the negation of the conclusion as `hne`.

Conclude with `hm (hsupp m (mem_support_iff.2 hne)).symm`. Establish `hc : c ≠ 0`. Introduce `h`. Apply `hg.1` to reduce the goal to its premises. Rewrite using `[h, C_0]`.

Establish `hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1` using `⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩`. Establish `hvan` using `(hg.2 1).2 hdvd`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by`. Assume the negation of the conclusion as `hne`. Take `⟨j, hj⟩` from `hW.isRelevant`.

Apply `hj` to reduce the goal to its premises. Establish `hrad : X j ∈ W.radical`. Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]`. Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `y hy`.

Distinguish the cases in `hy0 : y = 0`. Substitute `hy0` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd ⟨y, hy0, hy⟩ hne`. Rewrite `hrad` using `[hW.isPrime.radical]`. Then use the resulting hypothesis.

Establish `hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k` using `⟨x, hx0, hx, fun i => by simp⟩`. Use `hvan 0 hmem` as an intermediate fact. Simplify using `at this`.
-/
theorem ChowDegreePos.proof : ChowDegreePos.Statement := by
  intro n k δ W g hk hW hg hδ
  by_contra hlt
  have hδ0 : δ = 0 := by omega
  subst hδ0

  have hnt : NonTorsionWeight (groupWeight k n) := by
    intro m ij h
    have := congrFun h ij.1
    simpa [groupWeight] using this

  have hsupp : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    have h1 : Finsupp.weight (groupWeight k n) m = 0 := hδ (mem_support_iff.1 hm)
    ext ij
    exact (weightedDegree_eq_zero_iff hnt).1 h1 ij
  obtain ⟨c, rfl⟩ : ∃ c, g = C c := by
    refine ⟨coeff 0 g, ?_⟩
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (hsupp m (mem_support_iff.2 hne)).symm
  have hc : c ≠ 0 := by
    intro h
    apply hg.1
    rw [h, C_0]
  have hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1 :=
    ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hvan := (hg.2 1).2 hdvd

  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hW.isRelevant
    apply hj
    have hrad : X j ∈ W.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]
      rw [mem_vanishingIdeal_iff]
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp
      · exact absurd ⟨y, hy0, hy⟩ hne
    rwa [hW.isPrime.radical] at hrad
  have hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k :=
    ⟨x, hx0, hx, fun i => by simp⟩
  have := hvan 0 hmem
  simp at this

end GroundTheory.Heights₂.Heights
