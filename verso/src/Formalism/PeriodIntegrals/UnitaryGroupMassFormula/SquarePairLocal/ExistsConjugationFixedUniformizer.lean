import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.MemFixSub

noncomputable section
open NumberField

namespace PI.SqPairLocal.RU

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := by
  apply RingOfIntegers.ext
  rw [cj_coe, cj_coe, star_star]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_conjugation_fixed_uniformizer (hE : PI.IsCMUnram E) (Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (hc : Q.comap (cj E) = Q) : ∃ ϖ : 𝓞 E, cj E ϖ = ϖ ∧ ϖ ∈ Q ∧ ϖ ∉ Q ^ 2 := by
  have hcQ : ∀ y ∈ Q, cj E y ∈ Q := fun y hy => by
    rw [← Ideal.mem_comap, hc]; exact hy
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
  have hlt : Q ^ 2 < Q := by
    have := @Ideal.pow_succ_lt_pow _ _ _ Q hQ.isPrime hQ0 1
    rwa [pow_one] at this
  obtain ⟨x, hxQ, hx2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 Q hQ
  have htc : t = cj E θ := by
    apply RingOfIntegers.ext
    rw [cj_coe]
    exact ht
  subst htc
  have hrad : (Q ^ 2).radical = Q := by
    rw [Ideal.radical_pow _ two_ne_zero, hQ.isPrime.radical]
  have hprim : ∀ y, (θ - cj E θ) * y ∈ Q ^ 2 → y ∈ Q ^ 2 := by
    intro y hy
    have hP : (Q ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hQ)
    rw [mul_comm] at hy
    rcases (Ideal.isPrimary_iff.mp hP).2 hy with h | h
    · exact h
    · rw [hrad] at h
      exact absurd h hθt
  have hfix : ∀ y, cj E (y + cj E y) = y + cj E y := fun y => by
    rw [map_add, cj_cj, add_comm]
  have hcomb : (θ * x + cj E (θ * x)) - cj E θ * (x + cj E x) = (θ - cj E θ) * x := by
    rw [map_mul]; ring
  by_cases h2 : x + cj E x ∈ Q ^ 2
  · refine ⟨θ * x + cj E (θ * x), hfix _, ?_, ?_⟩
    · exact Q.add_mem (Q.mul_mem_left θ hxQ) (hcQ _ (Q.mul_mem_left θ hxQ))
    · intro h1
      apply hx2
      apply hprim
      rw [← hcomb]
      exact (Q ^ 2).sub_mem h1 ((Q ^ 2).mul_mem_left _ h2)
  · exact ⟨x + cj E x, hfix _, Q.add_mem hxQ (hcQ _ hxQ), h2⟩

end RU

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem realUnif : RealUnif := by
  intro E _ _ _ hE Q hQ hc
  exact RU.exists_conjugation_fixed_uniformizer hE Q hQ hc

end PI.SqPairLocal
