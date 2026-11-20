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
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cj_coe, cj_coe, star_star]`.
-/
theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := by
  apply RingOfIntegers.ext
  rw [cj_coe, cj_coe, star_star]

/- English proof (translation)
Establish `hcQ : ∀ y ∈ Q, cj E y ∈ Q` using `fun y hy => by`. Rewrite using `[← Ideal.mem_comap, hc]`. Conclude with `hy`. Establish `hQ0 : Q ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)`. Establish `hlt : Q ^ 2 < Q`.

Use `@Ideal.pow_succ_lt_pow _ _ _ Q hQ.isPrime hQ0 1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Take `⟨x, hxQ, hx2⟩` from `SetLike.exists_of_lt hlt`. Take `⟨θ, t, ht, hθt⟩` from `hE.2.2 Q hQ`. Establish `htc : t = cj E θ`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cj_coe]`. Conclude with `ht`. Substitute `htc` using the available equality. Establish `hrad : (Q ^ 2).radical = Q`.

Rewrite using `[Ideal.radical_pow _ two_ne_zero, hQ.isPrime.radical]`. Establish `hprim : ∀ y, (θ - cj E θ) * y ∈ Q ^ 2 → y ∈ Q ^ 2`. Introduce `y hy`. Establish `hP : (Q ^ 2).IsPrimary` using `Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hQ)`. Rewrite `hy` using `[mul_comm]`.

Break down `(Ideal.isPrimary_iff.mp hP).2 hy with h | h` into its components or cases. Conclude with `h`. Rewrite `h` using `[hrad]`. Conclude with `absurd h hθt`. Establish `hfix : ∀ y, cj E (y + cj E y) = y + cj E y` using `fun y => by`.

Rewrite using `[map_add, cj_cj, add_comm]`. Establish `hcomb : (θ * x + cj E (θ * x)) - cj E θ * (x + cj E x) = (θ - cj E θ) * x`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h2 : x + cj E x ∈ Q ^ 2`.

Use `⟨θ * x + cj E (θ * x), hfix _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Q.add_mem (Q.mul_mem_left θ hxQ) (hcQ _ (Q.mul_mem_left θ hxQ))`. Introduce `h1`. Apply `hx2` to reduce the goal to its premises. Apply `hprim` to reduce the goal to its premises.

Rewrite using `[← hcomb]`. Conclude with `(Q ^ 2).sub_mem h1 ((Q ^ 2).mul_mem_left _ h2)`. Conclude with `⟨x + cj E x, hfix _, Q.add_mem hxQ (hcQ _ hxQ), h2⟩`.
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
Introduce `E _ _ _ hE Q hQ hc`. Conclude with `RU.exists_conjugation_fixed_uniformizer hE Q hQ hc`.
-/
theorem realUnif : RealUnif := by
  intro E _ _ _ hE Q hQ hc
  exact RU.exists_conjugation_fixed_uniformizer hE Q hQ hc

end PI.SqPairLocal
