import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.StdPar
open scoped TensorProduct

namespace GlobalTheory.ColumnSpanCoefficients

/- English proof (translation)
Rewrite `hy` using `[colSpan]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Take `⟨j, rfl, hj⟩` from `hI i hi`.

Use `⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hj' hj`. Rewrite using `[Matrix.mulVec_single_one]`.

Use extensionality with `r`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨a, ha, rfl⟩` from `hx`.

Take `⟨b, hb, rfl⟩` from `hz`. Conclude with `⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩`.
-/
theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j : Fin s, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  classical
  rw [colSpan] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, rfl, hj⟩ := hI i hi
    refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hj' hj
    · rw [Matrix.mulVec_single_one]
      ext r
      rfl
  | zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩

end GlobalTheory.ColumnSpanCoefficients
