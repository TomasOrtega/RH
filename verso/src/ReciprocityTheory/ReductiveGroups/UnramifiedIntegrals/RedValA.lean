import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hD` using `discNeZero L`. Unfold `jInv`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jInv_sub_1728_eq_div (L : PeriodPair) :
    jInv L - 1728 = 1728 * 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  have hD := discNeZero L
  unfold jInv
  field_simp
  ring

/- English proof (translation)
Establish `hD` using `discNeZero L`. Rewrite using `[jInv_sub_1728_eq_div]`. Unfold `jInv`. Clear the denominators using the available nonvanishing facts.
-/
theorem jInv_ratio (L : PeriodPair) (h3 : L.g₃ ≠ 0) :
    27 * jInv L / (jInv L - 1728) = L.g₂ ^ 3 / L.g₃ ^ 2 := by
  have hD := discNeZero L
  rw [jInv_sub_1728_eq_div]
  unfold jInv
  field_simp

/- English proof (translation)
Take `⟨c, hc2⟩` from `IsAlgClosed.exists_pow_nat_eq (L.g₃ / L.g₂) (n := 2) (by norm_num)`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Establish `: L.g₃ / L.g₂ ≠ 0` using `div_ne_zero h3 h2`. Apply `this` to reduce the goal to its premises.

Rewrite using `[← hc2]`. Evaluate the numerical expressions. Take `⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩` from `homogeneity L c hc`. Use `⟨scalePair L c hc, hasCMByScale d L c hc hCM, jInvScale L c hc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg2, jInv_ratio L h3, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hg3, jInv_ratio L h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_cm_lattice_equal_invariants (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) :
    ∃ L0 : PeriodPair, HasCMBy d L0 ∧ jInv L0 = jInv L ∧
      L0.g₂ = 27 * jInv L / (jInv L - 1728) ∧ L0.g₃ = 27 * jInv L / (jInv L - 1728) := by
  obtain ⟨c, hc2⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₃ / L.g₂) (n := 2) (by norm_num)
  have hc : c ≠ 0 := by
    rintro rfl
    have : L.g₃ / L.g₂ ≠ 0 := div_ne_zero h3 h2
    apply this
    rw [← hc2]
    norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := homogeneity L c hc
  refine ⟨scalePair L c hc, hasCMByScale d L c hc hCM, jInvScale L c hc, ?_, ?_⟩
  · rw [hg2, jInv_ratio L h3, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    field_simp
  · rw [hg3, jInv_ratio L h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc2]
    field_simp

/- English proof (translation)
Establish `hD` using `discNeZero L`. Unfold `jInv`. Rewrite using `[div_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`.

Simplify using `using h`. Conclude with `absurd h hD`. Introduce `h left`. Rewrite using `[h]`. Evaluate the numerical expressions.
-/
theorem jInv_eq_zero_iff (L : PeriodPair) : jInv L = 0 ↔ L.g₂ = 0 := by
  have hD := discNeZero L
  unfold jInv
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

/- English proof (translation)
Establish `hD` using `discNeZero L`. Rewrite using `[← sub_eq_zero, jInv_sub_1728_eq_div, div_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Simplify using `using h`.

Conclude with `absurd h hD`. Introduce `h left`. Rewrite using `[h]`. Evaluate the numerical expressions.
-/
theorem jInv_eq_iff (L : PeriodPair) : jInv L = 1728 ↔ L.g₃ = 0 := by
  have hD := discNeZero L
  rw [← sub_eq_zero, jInv_sub_1728_eq_div, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · exact absurd h hD
  · intro h
    left
    rw [h]
    norm_num

end ReciprocityTheory.ChartRestriction.L1
