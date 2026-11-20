import Formalism.YangianSpanCharacter.StatementY

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.Y

section Helpers

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]`. Use `noncomm_ring`.
-/
private theorem mul_J_mul_transpose_apply_fin_two (b a : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (b * Formalism.YangianSpanCharacter.T.J A * aᵀ) i j = b i 0 * a j 1 - b i 1 * a j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]
  noncomm_ring

/- English proof (translation)
Establish `e` using `congrFun (congrFun (h Y) 0) 1`. Rewrite `e` using `[mul_J_mul_transpose_apply_fin_two]`. Rewrite using `[e]`. Simplify using `[Formalism.YangianSpanCharacter.T.J]`.
-/
lemma symplectic_transpose_entry_zero_one {t : 𝕜 → Matrix (Fin 2) (Fin 2) A} {q : 𝕜 → 𝕜}
    (h : ∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) (Y : 𝕜) :
    t Y 0 0 * t (Y + 1) 1 1 - t Y 0 1 * t (Y + 1) 1 0 = q Y • (1 : A) := by
  have e := congrFun (congrFun (h Y) 0) 1
  rw [mul_J_mul_transpose_apply_fin_two] at e
  rw [e]
  simp [Formalism.YangianSpanCharacter.T.J]

/- English proof (translation)
Establish `h1 : t Y 1 0 * t (Y + 1) 1 1 - t Y 1 1 * t (Y + 1) 1 0 = 0`. Establish `e` using `congrFun (congrFun (h Y) 1) 1`. Rewrite `e` using `[mul_J_mul_transpose_apply_fin_two]`. Rewrite using `[e]`. Simplify using `[Formalism.YangianSpanCharacter.T.J]`.

Conclude with `(sub_eq_zero.mp h1).symm`.
-/
lemma symplectic_transpose_entry_one_one {t : 𝕜 → Matrix (Fin 2) (Fin 2) A} {q : 𝕜 → 𝕜}
    (h : ∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) (Y : 𝕜) :
    t Y 1 1 * t (Y + 1) 1 0 = t Y 1 0 * t (Y + 1) 1 1 := by
  have h1 : t Y 1 0 * t (Y + 1) 1 1 - t Y 1 1 * t (Y + 1) 1 0 = 0 := by
    have e := congrFun (congrFun (h Y) 1) 1
    rw [mul_J_mul_transpose_apply_fin_two] at e
    rw [e]
    simp [Formalism.YangianSpanCharacter.T.J]
  exact (sub_eq_zero.mp h1).symm

end Helpers

/- English proof (translation)
Unfold `Formalism.YangianSpanCharacter.Y.QuasiDet`. Introduce `𝕜 A _ _ _ t τinv q S hL Y hY hY1`. Unfold `Formalism.YangianSpanCharacter.Y.ModHyp at hL`. Take `⟨-, -, h3, h4, -, -⟩` from `hL`. Establish `e2` using `symplectic_transpose_entry_zero_one h3 Y`.

Establish `e3` using `symplectic_transpose_entry_one_one h3 Y`. Take `⟨a1, -⟩` from `h4 (Y + 1) hY1`. Take `⟨-, b2⟩` from `h4 Y hY`. Establish `key : t (Y + 1) 1 0 = τinv Y * t Y 1 0 * t (Y + 1) 1 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `e4 : (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 = q Y • (1 : A)`. Rewrite using `[← e2, key]`. Use `noncomm_ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[a1, mul_one]`.

Use `_ = (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 * τinv (Y + 1) := (mul_assoc _ _ _).symm`. Use `_ = q Y • τinv (Y + 1) := by rw [e4, smul_mul_assoc, one_mul]`.
-/
theorem quasiDeterminant : Formalism.YangianSpanCharacter.Y.QuasiDet := by
  unfold Formalism.YangianSpanCharacter.Y.QuasiDet
  intro 𝕜 A _ _ _ t τinv q S hL Y hY hY1
  unfold Formalism.YangianSpanCharacter.Y.ModHyp at hL
  obtain ⟨-, -, h3, h4, -, -⟩ := hL
  have e2 := symplectic_transpose_entry_zero_one h3 Y
  have e3 := symplectic_transpose_entry_one_one h3 Y
  obtain ⟨a1, -⟩ := h4 (Y + 1) hY1
  obtain ⟨-, b2⟩ := h4 Y hY
  have key : t (Y + 1) 1 0 = τinv Y * t Y 1 0 * t (Y + 1) 1 1 := by
    calc t (Y + 1) 1 0 = τinv Y * t Y 1 1 * t (Y + 1) 1 0 := by rw [b2, one_mul]
      _ = τinv Y * (t Y 1 1 * t (Y + 1) 1 0) := mul_assoc _ _ _
      _ = τinv Y * (t Y 1 0 * t (Y + 1) 1 1) := by rw [e3]
      _ = τinv Y * t Y 1 0 * t (Y + 1) 1 1 := (mul_assoc _ _ _).symm
  have e4 : (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 = q Y • (1 : A) := by
    rw [← e2, key]
    noncomm_ring
  calc t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0
        = (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * (t (Y + 1) 1 1 * τinv (Y + 1)) := by
          rw [a1, mul_one]
    _ = (t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0) * t (Y + 1) 1 1 * τinv (Y + 1) :=
          (mul_assoc _ _ _).symm
    _ = q Y • τinv (Y + 1) := by rw [e4, smul_mul_assoc, one_mul]

/- English proof (translation)
Unfold `Formalism.YangianSpanCharacter.Y.ModHypModel Formalism.YangianSpanCharacter.Y.ModHyp`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u v i j k l dsimp only`. Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `Y`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Evaluate the numerical expressions using `[Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`. Introduce `Y`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Evaluate the numerical expressions using `[Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`. Introduce `u _`. Evaluate the numerical expressions.

Introduce `u v`. Conclude with `Commute.all _ _`. Introduce `u v`. Conclude with `Commute.all _ _`.
-/
theorem isLaxFamilyConstantModel : Formalism.YangianSpanCharacter.Y.ModHypModel := by
  unfold Formalism.YangianSpanCharacter.Y.ModHypModel Formalism.YangianSpanCharacter.Y.ModHyp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v i j k l
    dsimp only
    rw [smul_eq_mul]
    ring
  · intro Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
  · intro Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
  · intro u _
    norm_num
  · intro u v
    exact Commute.all _ _
  · intro u v
    exact Commute.all _ _

end Formalism.YangianSpanCharacter.P
