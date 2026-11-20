import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ v N`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`.

Conclude with `Valuation.map_add_le _ ih (le_of_eq (map_one _))`.
-/
theorem valued_natCast_adicCompletion_le_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ),
    Valued.v ((N : v.adicCompletion F)) ≤ 1 := by
  intro F _ _ v N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (le_of_eq (map_one _))

end GlobalTheory
