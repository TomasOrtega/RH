import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Establish an intermediate fact. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. It suffices to derive a contradiction.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem hExpInj_of : HExpInj := by
  intro F _ _ n t₀ ε lam h hanti hh i k hik
  rcases hh with ⟨m, -, hh⟩ | ⟨m, -, hh⟩
  · rw [hh i, hh k] at hik
    have hi := i.isLt
    have hk := k.isLt
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti t₀ hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti t₀ hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega
  · rw [hh i, hh k] at hik
    have si : ∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) i =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have sk : ∑ j ∈ Finset.univ.erase k, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) k =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega

end UpperTheory.Gal.LocalSmoothExtension
