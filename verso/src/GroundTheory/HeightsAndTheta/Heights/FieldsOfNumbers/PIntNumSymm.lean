import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {K : Type*}

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [diffStep, sub_sub, add_comm a b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_sub, add_comm a b]
  ring

instance diffStep_leftCommutative :
    LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) :=
  ⟨diffStep_comm⟩

/- English proof (translation)
Unfold `mixedDiff`. Conclude with `(σ.ofFn_comp_perm bs).foldr_eq h`.
-/
theorem mixedDiff_comp_perm {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by
  unfold mixedDiff
  exact (σ.ofFn_comp_perm bs).foldr_eq h

end

/- English proof (translation)
Introduce `F _ K _ _ ι _ I n bs σ`. Unfold `intNum`. Rewrite using `[mixedDiff_comp_perm]`.
-/
theorem IntNumSymm.proof : IntNumSymm.Statement := by
  intro F _ K _ _ ι _ I n bs σ
  unfold intNum
  rw [mixedDiff_comp_perm]

end GroundTheory.Heights₂.Heights.FieldNumbers
