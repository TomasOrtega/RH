import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

/- English proof (translation)
Introduce `L _ _ O hft _ m _`. Establish `hq : Algebra.FiniteType ℤ (O ⧸ m)` using `@Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m) (Ideal.Quotient.mkₐ_surjective ℤ m)`. Set `_ : Field (O ⧸ m)` to `Ideal.Quotient.field m`. Apply the tactic sequence `obtain ⟨hp, -⟩ := @natCard_eq_pow_length_of_finiteType (O ⧸ m) _ (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)`. Use `set p := ringChar (O ⧸ m)`.

Establish `hpm : (p : O) ∈ m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero (O ⧸ m) p`. Establish `hp0 : (p : L) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Use `(FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_` and prove the remaining obligations.

Establish `hlt` using `(hw.2 (p : O)).mpr hpm`. Establish `hcoe : ((p : O) : L) = (p : L)` using `by simp`. Rewrite `hlt` using `[hcoe]`. Conclude with `hlt.ne`.
-/
theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
