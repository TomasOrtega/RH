import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.MassSt
import Mathlib

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [conjO_coe, star_star]`.
-/
theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  simp only [conjO_coe, star_star]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]`. Introduce and unpack `r ⟨s, hs, h⟩`. Use `show conjO K r ∈ P`. Establish `hrs : conjO K r = s`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[conjO_coe]`. Conclude with `(congrArg star h).trans (star_star _)`. Rewrite using `[hrs]`. Conclude with `hs`.

Introduce `r hr`. Rewrite using `[Formalism.HermitianLatticesTheory.conjIdeal]`. Apply `Ideal.subset_span` to reduce the goal to its premises. Use `⟨conjO K r, hr, ?_⟩` and prove the remaining obligations. Use `show (r : K) = star ((conjO K r : 𝓞 K) : K)`.

Rewrite using `[conjO_coe, star_star]`.
-/
theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  apply le_antisymm
  · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
    rintro r ⟨s, hs, h⟩
    show conjO K r ∈ P
    have hrs : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      exact (congrArg star h).trans (star_star _)
    rw [hrs]
    exact hs
  · intro r hr
    rw [Formalism.HermitianLatticesTheory.conjIdeal]
    apply Ideal.subset_span
    refine ⟨conjO K r, hr, ?_⟩
    show (r : K) = star ((conjO K r : 𝓞 K) : K)
    rw [conjO_coe, star_star]

/- English proof (translation)
Take `⟨-, -, h3⟩` from `hK`. Take `⟨θ, t, ht, hθ⟩` from `h3 P hP`. Use `⟨θ, ?_⟩` and prove the remaining obligations. Establish `htθ : conjO K θ = t`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[conjO_coe]`. Conclude with `ht.symm`. Rewrite using `[htθ]`. Conclude with `hθ`.
-/
theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨-, -, h3⟩ := hK
  obtain ⟨θ, t, ht, hθ⟩ := h3 P hP
  refine ⟨θ, ?_⟩
  have htθ : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rw [htθ]
  exact hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

end WithF

end ReciprocityTheory.ChartRestriction.L3
