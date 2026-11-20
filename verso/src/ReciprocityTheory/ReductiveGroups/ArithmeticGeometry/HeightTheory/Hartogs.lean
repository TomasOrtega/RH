import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

/- English proof (translation)
Establish `key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c = algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a`. Introduce `c`. Proceed by induction on `c using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro h0`. Conclude with `absurd rfl h0`.

Consider the case `h₂ u hu`. Introduce `_ a0 hx`. Use `⟨a0 * ↑(hu.unit⁻¹), ?_⟩` and prove the remaining obligations. Establish `hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1`. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu', mul_one]`. Use `_ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]`. Consider the case `h₃ c p hc hp ih`.

Introduce `_ a0 hx`. Take `⟨a, b, hpb, hab⟩` from `h p hp`. Establish `hinj` using `IsFractionRing.injective R (FractionRing R)`. Establish `e1 : a * (p * c) = a0 * b`. Apply `hinj` to reduce the goal to its premises.

Simplify using `only [map_mul] at hx hab ⊢`. Take the linear combination `(-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab + algebraMap R (FractionRing R) b * hx`. Establish `hpa0 : p ∣ a0`. Establish `: p ∣ a0 * b` using `⟨a * c, by rw [← e1]; ring⟩`. Break down `hp.dvd_or_dvd this with h1 | h1` into its components or cases.

Conclude with `h1`. Conclude with `absurd h1 hpb`. Take `⟨a1, rfl⟩` from `hpa0`. Establish `hp0 : algebraMap R (FractionRing R) p ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap R (FractionRing R))]`.

Conclude with `fun h' => hp.ne_zero (hinj h')`. Use `ih hc a1 ?_` and prove the remaining obligations. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises. Simplify using `only [map_mul] at hx ⊢`. Take the linear combination `hx`.

Take `⟨a0, c, hc, rfl⟩` from `IsFractionRing.div_surjective (A := R) x`. Establish `hc0 : c ≠ 0` using `nonZeroDivisors.ne_zero hc`. Use `key c hc0 a0 ?_` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀]`. Rewrite using `[Ne, ← map_zero (algebraMap R (FractionRing R))]`.

Conclude with `fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')`.
-/
theorem ufd_mem_of_forall_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x : FractionRing R)
    (h : ∀ p : R, Prime p → ∃ a b : R, ¬ p ∣ b ∧ x * algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) a) :
    ∃ a : R, x = algebraMap R (FractionRing R) a := by
  classical
  have key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c =
      algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a := by
    intro c
    induction c using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h0; exact absurd rfl h0
    | h₂ u hu =>
      intro _ a0 hx
      refine ⟨a0 * ↑(hu.unit⁻¹), ?_⟩
      have hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1 := by
        rw [← map_mul]; simp
      calc x = x * (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹)) := by
              rw [hu', mul_one]
        _ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]
    | h₃ c p hc hp ih =>
      intro _ a0 hx
      obtain ⟨a, b, hpb, hab⟩ := h p hp
      have hinj := IsFractionRing.injective R (FractionRing R)
      have e1 : a * (p * c) = a0 * b := by
        apply hinj
        simp only [map_mul] at hx hab ⊢
        linear_combination (-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab +
          algebraMap R (FractionRing R) b * hx
      have hpa0 : p ∣ a0 := by
        have : p ∣ a0 * b := ⟨a * c, by rw [← e1]; ring⟩
        rcases hp.dvd_or_dvd this with h1 | h1
        · exact h1
        · exact absurd h1 hpb
      obtain ⟨a1, rfl⟩ := hpa0
      have hp0 : algebraMap R (FractionRing R) p ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
        exact fun h' => hp.ne_zero (hinj h')
      refine ih hc a1 ?_
      apply mul_left_cancel₀ hp0
      simp only [map_mul] at hx ⊢
      linear_combination hx
  obtain ⟨a0, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine key c hc0 a0 ?_
  rw [div_mul_cancel₀]
  rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
  exact fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')

end ReciprocityTheory.ChartRestriction.G.T0
