import Mathlib

namespace GlobalTheory.MapOfRealOne

/- English proof (translation)
Introduce `d1 m inst`. Conclude with `Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one`.
-/
theorem map_ofReal_one :
    (let d1 : {m n : Type} → Matrix m n ℝ → Matrix m n ℂ := @(fun {m n : Type} (M : Matrix m n ℝ) ↦ Matrix.map M fun (t : ℝ) ↦ (↑t : ℂ)); ∀ {m : Type} [inst : DecidableEq m], d1 (1 : Matrix m m ℝ) = (1 : Matrix m m ℂ)) := by
  intro d1 m inst
  exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

end GlobalTheory.MapOfRealOne
