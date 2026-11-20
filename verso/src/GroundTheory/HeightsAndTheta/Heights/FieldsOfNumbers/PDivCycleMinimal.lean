import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by`. Establish `h2` using `PFContracted.ringKrullDim_lt_top Q`. Consider the cases of `hc : ringKrullDim (MRing ι F ⧸ Q) with`. Consider the case `bot`. Rewrite `h` using `[relDim, hc]`.

Conclude with `absurd h (by simp)`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`. Rewrite `h2` using `[hc]`.

Conclude with `absurd h2 (by simp)`. Consider the case `coe d => exact ⟨d, rfl⟩`. Rewrite `h` using `[PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop]`. Establish `h' : (d : ℤ) - Fintype.card K = m`. Use `WithBot.coe_injective h` as an intermediate fact.

Conclude with `WithTop.coe_injective this` after adjusting the coercions. Rewrite using `[hd]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem DivCycleMinimal.ringKrullDim_eq {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by
    have h2 := PFContracted.ringKrullDim_lt_top Q
    cases hc : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [relDim, hc] at h
      exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [hc] at h2
        exact absurd h2 (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop] at h
  have h' : (d : ℤ) - Fintype.card K = m := by
    have := WithBot.coe_injective h
    exact_mod_cast WithTop.coe_injective this
  rw [hd]
  congr 1
  omega

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle`. Establish `hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes`. Use `⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩` and prove the remaining obligations. Take `⟨hQp, hJQ⟩` from `hQ`. Assume the negation of the conclusion as `hWQ`.

Take `⟨f, hfW, hfQ⟩` from `Set.not_subset.mp hWQ`. Establish `h1` using `PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW`. Establish `h2` using `PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))`. Establish `h3` using `(add_le_add h1 (le_refl 1)).trans h2`. Rewrite `h3` using `[DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn]`.

Establish `h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ))`. Simplify `h3` using `only [Nat.cast_add, Nat.cast_one]`. Establish `h5` using `WithBot.coe_le_coe.mp h4`. Establish `h6` using `ENat.natCast_le_natCast.mp h5`. Use linear arithmetic over natural numbers and integers.

Conclude with `⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩`.
-/
theorem DivCycleMinimal.proof : DivCycleMinimal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle
  have hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩
    obtain ⟨hQp, hJQ⟩ := hQ
    by_contra hWQ
    obtain ⟨f, hfW, hfQ⟩ := Set.not_subset.mp hWQ
    have h1 := PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW
    have h2 := PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    have h3 := (add_le_add h1 (le_refl 1)).trans h2
    rw [DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn] at h3
    have h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 := ENat.natCast_le_natCast.mp h5
    omega
  exact ⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
