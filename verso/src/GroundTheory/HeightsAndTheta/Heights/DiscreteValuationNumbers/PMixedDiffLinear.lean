import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section MixedDiffLinearProof

variable {K : Type*}

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [diffStep, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diffStep_add' (b : K → ℤ) (f g : (K → ℤ) → ℤ) :
    diffStep b (f + g) = diffStep b f + diffStep b g := by
  funext m; simp only [diffStep, Pi.add_apply]; ring

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [diffStep, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diffStep_smul' (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by
  funext m; simp only [diffStep, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [diffStep, shiftFn, sub_right_comm]`.
-/
theorem diffStep_shiftFn' (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by
  funext m; simp only [diffStep, shiftFn, sub_right_comm]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `only [diffStep, sub_right_comm m b b']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diffStep_comm' (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by
  funext m; simp only [diffStep, sub_right_comm m b b']; ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨rfl, rfl, rfl, rfl⟩`. Consider the case `cons a l ih`. Take `⟨h1, h2, h3, h4⟩` from `ih`. Simplify using `only [List.foldr_cons]`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, diffStep_add']`. Rewrite using `[h2, diffStep_smul']`. Rewrite using `[h3, diffStep_shiftFn']`. Rewrite using `[h4, diffStep_comm']`.
-/
theorem foldr_diffStep_props (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, diffStep_add']
    · rw [h2, diffStep_smul']
    · rw [h3, diffStep_shiftFn']
    · rw [h4, diffStep_comm']

/- English proof (translation)
Introduce `K n bs f g c s b`. Take `⟨h1, h2, h3, h4⟩` from `foldr_diffStep_props (List.ofFn bs) f g c s b`. Use `⟨h1, h2, h3, h4, ?_⟩` and prove the remaining obligations. Unfold `mixedDiff`. Rewrite using `[List.ofFn_succ]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]`.
-/
theorem MixedDiffLinear.proof : MixedDiffLinear.Statement := by
  intro K n bs f g c s b
  obtain ⟨h1, h2, h3, h4⟩ := foldr_diffStep_props (List.ofFn bs) f g c s b
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]

end MixedDiffLinearProof

end GroundTheory.Heights₂.Heights.NumbersDVR
