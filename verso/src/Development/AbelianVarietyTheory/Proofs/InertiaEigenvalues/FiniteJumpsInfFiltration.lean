import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hanti : Antitone F` using `antitone_int_of_succ_le hF`. Establish `hfin : ∀ a, Module.Finite E ↥(D ⊓ F a)` using `fun a => Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left`. Establish `key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b → Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a)`. Introduce `a b ha hab`. Use `haveI := hfin a`.

Apply `Submodule.finrank_lt_finrank_of_lt` to reduce the goal to its premises. Establish `h1 : D ⊓ F b ≤ D ⊓ F (a + 1)` using `inf_le_inf_left _ (hanti (by omega))`. Establish `h2 : D ⊓ F (a + 1) < D ⊓ F a` using `lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha`. Conclude with `lt_of_le_of_lt h1 h2`. Use `Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a)) (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)` and prove the remaining obligations.

Introduce `a _`. Conclude with `Submodule.finrank_mono inf_le_left`. Introduce `a ha b hb hab`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Conclude with `absurd hab (key a b ha h).ne'`.

Conclude with `h`. Conclude with `absurd hab (key b a hb h).ne`.
-/
theorem finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne

end GlobalTheory
