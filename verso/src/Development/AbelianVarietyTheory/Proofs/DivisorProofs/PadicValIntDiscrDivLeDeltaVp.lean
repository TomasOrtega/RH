import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `h` using `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)`. Establish `hL : (discr L).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero L)`. Rewrite `hL` using `[h]`. Unfold `padicValInt`.

Rewrite using `[h, padicValNat.mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL), padicValNat.pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, padicValNat.mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL), padicValNat.pow]
  omega

/- English proof (translation)
Introduce `E _ _ _ l hl`. Establish `h` using `finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl`. Establish `h2` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Establish `hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E)` using `by exact_mod_cast Module.finrank_pos`. Establish `hE : (0 : ℝ) < Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp`. Rewrite using `[div_le_div_iff₀ hF hE, ← h2]`. Establish `h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤ padicValInt l (discr E)` using `by exact_mod_cast h`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
