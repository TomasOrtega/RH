import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem Ext.w_add_le_max (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (x y : AlgebraicClosure F) : e.w (x + y) ≤ max (e.w x) (e.w y) := by
  have key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      have ha : a = 0 := e.w.eq_zero.1 (le_antisymm (by simpa using hab) (e.w.nonneg a))
      simp [ha]
    · have hwb : 0 < e.w b := e.w.pos hb
      have h1 : a / b ∈ e.O := by
        rw [e.mem_O, map_div₀]
        exact (div_le_one hwb).2 hab
      have h2 : 1 + a / b ∈ e.O := e.O.add_mem _ _ e.O.one_mem h1
      have h3 : e.w (1 + a / b) ≤ 1 := (e.mem_O _).1 h2
      have h4 : a + b = b * (1 + a / b) := by field_simp; ring
      rw [h4, map_mul]
      exact mul_le_of_le_one_right (e.w.nonneg b) h3
  rcases le_total (e.w x) (e.w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]; exact (key y x h).trans (le_max_left _ _)

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (x y : AlgebraicClosure F),
    e.w (x + y) ≤ max (e.w x) (e.w y) := Ext.w_add_le_max

end GlobalTheory.TrueGeo
