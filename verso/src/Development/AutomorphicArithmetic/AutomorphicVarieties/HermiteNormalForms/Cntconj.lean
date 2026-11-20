import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsep

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Move the embeddings inside the algebraic operations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
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
