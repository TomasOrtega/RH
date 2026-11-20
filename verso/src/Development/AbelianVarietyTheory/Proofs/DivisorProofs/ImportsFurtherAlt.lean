import Mathlib

namespace GlobalTheory.RealEmbeddingLemmaSecond

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem main :
    (let d1 : {m n : Type} → Matrix m n ℝ → Matrix m n ℂ :=
        @(fun {m n : Type} (M : Matrix m n ℝ) ↦ Matrix.map M fun (t : ℝ) ↦ (↑t : ℂ));
      ∀ {m n : Type} (M N : Matrix m n ℝ), d1 (M - N) = d1 M - d1 N) := by
  intro d1 m n M N
  ext i j
  simp [d1, Matrix.map_apply, Matrix.sub_apply]

end GlobalTheory.RealEmbeddingLemmaSecond
