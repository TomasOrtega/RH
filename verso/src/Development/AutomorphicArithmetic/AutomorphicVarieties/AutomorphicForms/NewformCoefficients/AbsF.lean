import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

/- English proof (translation)
Establish `a1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1` using `Subring.mem_iInf.1 hu.1 w`. Establish `a2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1` using `Subring.mem_iInf.1 hu.2 w`. Establish `a3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Use `le_antisymm a1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem val_one (u : (Af ℚ)ˣ) (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have a1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have a2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have a3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

/- English proof (translation)
Introduce `r hr u hu`. Take `⟨-, h2, h3, h4⟩` from `UpperTheory.V.Sd.Hm.absf ℚ`. Rewrite using `[h2, h3 u (val_one u hu), mul_one]`. Establish `h` using `h4 r`. Establish `hr' : (0 : ℝ) < ((r : ℚ) : ℝ)` using `by exact_mod_cast hr`.

Establish `e : (∏ v, |reAt v (r : ℚ)|) = ((r : ℚ) : ℝ)`. Rewrite using `[Fintype.prod_subsingleton _ Rat.infinitePlace, reAt, eq_ratCast]`. Simplify using `[abs_of_pos hr']`. Rewrite `h` using `[e]`. Conclude with `eq_inv_of_mul_eq_one_right h`.
-/
theorem UpperTheory.V.Af.Nf.absF :
    UpperTheory.V.Af.Nf.AbsF := by
  intro r hr u hu
  obtain ⟨-, h2, h3, h4⟩ := UpperTheory.V.Sd.Hm.absf ℚ
  rw [h2, h3 u (val_one u hu), mul_one]
  have h := h4 r
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have e : (∏ v, |reAt v (r : ℚ)|) = ((r : ℚ) : ℝ) := by
    rw [Fintype.prod_subsingleton _ Rat.infinitePlace, reAt, eq_ratCast]
    simp [abs_of_pos hr']
  rw [e] at h
  exact eq_inv_of_mul_eq_one_right h
