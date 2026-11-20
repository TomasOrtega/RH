import Mathlib

/- English proof (translation)
Introduce `G _ _ χ hχ`. Establish `hne : (Units.coeHom ℂ).comp χ ≠ 1`. Introduce `h`. Apply `hχ` to reduce the goal to its premises. Use extensionality with `z`.

Establish `hz` using `DFunLike.congr_fun h z`. Simplify using `using hz`. Simplify using `using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne`.
-/
theorem UpperTheory.Reformulated.B.Qe46.sum_char :
    ∀ {G : Type} [inst : CommGroup G] [inst_1 : Fintype G] (χ : G →* ℂˣ),
    χ ≠ (1 : G →* ℂˣ) → ∑ z : G, (↑((χ : G → ℂˣ) z) : ℂ) = (0 : ℂ) := by
  intro G _ _ χ hχ
  have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext z
    have hz := DFunLike.congr_fun h z
    simpa using hz
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne
