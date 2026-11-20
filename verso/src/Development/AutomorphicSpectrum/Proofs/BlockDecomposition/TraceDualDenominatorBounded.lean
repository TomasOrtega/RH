import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

/- English proof (translation)
Introduce `F _ _`. Take `⟨a, ha, hint⟩` from `(FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Use `⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `ha0`. Introduce `f hf`. Establish `hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)`. Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]`. Introduce `x hx`.

Take `⟨r, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Take `⟨m, hm⟩` from `hf r`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, eq_intCast]`. Conclude with `hm.symm`.

Take `⟨o, ho⟩` from `hint f hmem`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))`. Use `⟨c * o, ?_⟩` and prove the remaining obligations. Rewrite `ho` using `[Algebra.smul_def]`. Use `show algebraMap (𝓞 F) F (c * o) = _`.

Rewrite using `[map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]`.
-/
theorem traceDual_clear_by_integer : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  intro F _ _
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · intro f hf
    have hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]
      intro x hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      obtain ⟨m, hm⟩ := hf r
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, eq_intCast]
      exact hm.symm
    obtain ⟨o, ho⟩ := hint f hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨c * o, ?_⟩
    rw [Algebra.smul_def] at ho
    show algebraMap (𝓞 F) F (c * o) = _
    rw [map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]

end GlobalTheory.CompanionTheory.SiegelND.Integ
