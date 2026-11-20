import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

/- English proof (translation)
Introduce `Ω _ B X η _ f hfin hX hf0 hc hloc`. Establish `: Module.Finite ℤ B` using `hfin`. Establish `: IsNoetherianRing B` using `IsNoetherianRing.of_finite ℤ B`. Set `K : η → Ideal B` to `fun i => { carrier := {t : B | (t : Ω) * f i ∈ X} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at ha hb ⊢`.

Conclude with `X.add_mem ha hb`. Use the proof step `zero_mem' := by simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact X.zero_mem`. Use the proof step `smul_mem' := fun c t ht => by`. Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ht ⊢`. Conclude with `hX _ c.2 _ ht }`.

Establish `hK : ∀ i, ∀ t : B, t ∈ K i ↔ (t : Ω) * f i ∈ X` using `fun _ _ => Iff.rfl`. Establish `hfg : ∀ i, ∃ T : Finset B, Ideal.span (T : Set B) = K i` using `fun i => IsNoetherian.noetherian (K i)`. Use `choose T hT using hfg`. Use `⟨?_, Σ i : η, {t : B // t ∈ T i}, inferInstance, fun j => (j.2.1 : Ω) * f j.1, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `Ideal.exists_maximal B`.

Take `⟨i, ⟨b, hbm, hbX⟩, -⟩` from `hloc m hm`. Establish `hb : (b : Ω) ≠ 0`. Introduce `h`. Conclude with `hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)`. Introduce `hbot`.

Rewrite `hbX` using `[hbot, AddSubgroup.mem_bot]`. Conclude with `mul_ne_zero hb (hf0 i) hbX`. Introduce and unpack `⟨i, t, ht⟩`. Rewrite using `[← hK, ← hT i]`. Conclude with `Ideal.subset_span ht`.

Introduce and unpack `⟨i, t, -⟩`. Take `⟨c, hcB, hc0, hcf⟩` from `hc i`. Use `⟨c, hcB, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `B.mul_mem t.2 hcf`.

Introduce `m hm`. Take `⟨i, ⟨b, hbm, hbX⟩, hall⟩` from `hloc m hm`. Establish `: ∃ t ∈ T i, t ∉ m`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`.

Establish `hle : K i ≤ m`. Rewrite using `[← hT i, Ideal.span_le]`. Conclude with `fun t ht => hno t ht`. Conclude with `hbm (hle ((hK i b).2 hbX))`. Take `⟨t, htT, htm⟩` from `this`.

Use `⟨⟨i, t, htT⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨b', c', hb'm, hbz⟩` from `hall z hz`. Use `⟨t * b', c', fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `hm.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `htm h`.

Conclude with `hb'm h`. Simplify using `only [Subring.coe_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem LocalGenFamily.proof : LocalGenFamily.Statement := by
  intro Ω _ B X η _ f hfin hX hf0 hc hloc
  have : Module.Finite ℤ B := hfin
  have : IsNoetherianRing B := IsNoetherianRing.of_finite ℤ B

  let K : η → Ideal B := fun i =>
    { carrier := {t : B | (t : Ω) * f i ∈ X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact X.add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact X.zero_mem
      smul_mem' := fun c t ht => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ht ⊢
        exact hX _ c.2 _ ht }
  have hK : ∀ i, ∀ t : B, t ∈ K i ↔ (t : Ω) * f i ∈ X := fun _ _ => Iff.rfl
  have hfg : ∀ i, ∃ T : Finset B, Ideal.span (T : Set B) = K i := fun i => IsNoetherian.noetherian (K i)
  choose T hT using hfg
  refine ⟨?_, Σ i : η, {t : B // t ∈ T i}, inferInstance, fun j => (j.2.1 : Ω) * f j.1, ?_, ?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    obtain ⟨i, ⟨b, hbm, hbX⟩, -⟩ := hloc m hm
    have hb : (b : Ω) ≠ 0 := by
      intro h
      exact hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
    intro hbot
    rw [hbot, AddSubgroup.mem_bot] at hbX
    exact mul_ne_zero hb (hf0 i) hbX
  · rintro ⟨i, t, ht⟩
    rw [← hK, ← hT i]
    exact Ideal.subset_span ht
  · rintro ⟨i, t, -⟩
    obtain ⟨c, hcB, hc0, hcf⟩ := hc i
    refine ⟨c, hcB, hc0, ?_⟩
    rw [mul_left_comm]
    exact B.mul_mem t.2 hcf
  · intro m hm
    obtain ⟨i, ⟨b, hbm, hbX⟩, hall⟩ := hloc m hm
    have : ∃ t ∈ T i, t ∉ m := by
      by_contra hno
      push Not at hno
      have hle : K i ≤ m := by
        rw [← hT i, Ideal.span_le]
        exact fun t ht => hno t ht
      exact hbm (hle ((hK i b).2 hbX))
    obtain ⟨t, htT, htm⟩ := this
    refine ⟨⟨i, t, htT⟩, fun z hz => ?_⟩
    obtain ⟨b', c', hb'm, hbz⟩ := hall z hz
    refine ⟨t * b', c', fun h => ?_, ?_⟩
    · rcases hm.isPrime.mem_or_mem h with h | h
      · exact htm h
      · exact hb'm h
    · simp only [Subring.coe_mul]
      calc (t : Ω) * b' * z = t * (b' * z) := by ring
        _ = t * (c' * f i) := by rw [hbz]
        _ = c' * (t * f i) := by ring

end GroundTheory.Heights₂.Heights.Targets
