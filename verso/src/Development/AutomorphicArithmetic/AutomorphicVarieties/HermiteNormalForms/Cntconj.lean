import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsep

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ R`. Establish `hq : 2 * R + 1 ≠ 0` using `by omega`. Establish `hsep : ∀ a ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ b ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ x : 𝓞 L, a - b = (2 * R + 1) • x → a = b`. Introduce `a ha b hb x hab`. Distinguish the cases in `hx : x = 0`.

Rewrite `hab` using `[hx, smul_zero, sub_eq_zero]`. Conclude with `hab`. It suffices to derive a contradiction. Establish `key : ∀ w : InfinitePlace L, w (x : L) < 1`. Introduce `w`.

Establish `h1 : ‖embO w (a - b)‖ ≤ 2 * R`. Rewrite using `[map_sub]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[hab, map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast]`. Establish `hn : ‖embO w x‖ = w (x : L)` using `InfinitePlace.norm_embedding_eq w (x : L)`.

Rewrite `h1` using `[hn]`. Move the coercions through the operations in `at h1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: (2 * (R : ℝ) + 1) * 1 ≤ (2 * (R : ℝ) + 1) * w (x : L)` using `mul_le_mul_of_nonneg_left hc (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨w0⟩` from `(inferInstance : Nonempty (InfinitePlace L))`. Use `InfinitePlace.one_le_of_lt_one (w := w0) hx (fun z _ => key z)` as an intermediate fact. Combine the linear relations using `[key w0]`. Take `⟨hfin, hcard⟩` from `cardsep (𝓞 L) (2 * R + 1) hq _ hsep`.

Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite `hcard` using `[RingOfIntegers.rank]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.KT.cntconj :
    ∀ (L : Type) [Field L] [NumberField L] (R : ℕ),
    {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.Finite ∧
      {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.ncard ≤ (2 * R + 1) ^ Module.finrank ℚ L := by
  intro L _ _ R
  have hq : 2 * R + 1 ≠ 0 := by omega
  have hsep : ∀ a ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ b ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R},
      ∀ x : 𝓞 L, a - b = (2 * R + 1) • x → a = b := by
    intro a ha b hb x hab
    by_cases hx : x = 0
    · rw [hx, smul_zero, sub_eq_zero] at hab
      exact hab
    exfalso
    have key : ∀ w : InfinitePlace L, w (x : L) < 1 := by
      intro w
      have h1 : ‖embO w (a - b)‖ ≤ 2 * R := by
        rw [map_sub]
        calc ‖embO w a - embO w b‖ ≤ ‖embO w a‖ + ‖embO w b‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (ha w) (hb w)
          _ = 2 * R := by ring
      rw [hab, map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h1
      have hn : ‖embO w x‖ = w (x : L) := InfinitePlace.norm_embedding_eq w (x : L)
      rw [hn] at h1
      push_cast at h1
      by_contra hc
      push_neg at hc
      have : (2 * (R : ℝ) + 1) * 1 ≤ (2 * (R : ℝ) + 1) * w (x : L) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      linarith
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have := InfinitePlace.one_le_of_lt_one (w := w0) hx (fun z _ => key z)
    linarith [key w0]
  obtain ⟨hfin, hcard⟩ := cardsep (𝓞 L) (2 * R + 1) hq _ hsep
  refine ⟨hfin, ?_⟩
  rwa [RingOfIntegers.rank] at hcard
