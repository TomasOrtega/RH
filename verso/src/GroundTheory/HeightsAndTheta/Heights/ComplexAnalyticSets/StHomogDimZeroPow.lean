import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

def HomogDimZeroPow.Statement : Prop :=
  ∀ (n : ℕ) (K : Ideal (MvPolynomial (Fin n) ℂ)),
    K.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) ≤ 0 → ∃ N : ℕ, originIdeal n ^ N ≤ K

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[originIdeal, ← Set.image_univ, mem_ideal_span_X_image, RingHom.mem_ker, constantCoeff_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `h0`.

Take `⟨i, -, hi⟩` from `h 0 (mem_support_iff.2 h0)`. Conclude with `hi rfl`. Introduce `h m hm`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Conclude with `mem_support_iff.1 hm h`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.1 hm0`. Conclude with `⟨i, Set.mem_univ _, hi⟩`.
-/
theorem originIdeal_eq_ker (n : ℕ) :
    originIdeal n = RingHom.ker (constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  ext f
  rw [originIdeal, ← Set.image_univ, mem_ideal_span_X_image, RingHom.mem_ker, constantCoeff_eq]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.2 h0)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact mem_support_iff.1 hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
    exact ⟨i, Set.mem_univ _, hi⟩

/- English proof (translation)
Rewrite using `[originIdeal_eq_ker]`. Conclude with `RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)`.
-/
theorem originIdeal_isMaximal (n : ℕ) : (originIdeal n).IsMaximal := by
  rw [originIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)

end

end GroundTheory.Heights₂.Heights.ComplexSets
