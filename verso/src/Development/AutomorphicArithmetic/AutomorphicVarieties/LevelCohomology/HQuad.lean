import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

/- English proof (translation)
Introduce `K _ _ l hl h5 hn hd`. Establish `h` using `GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Establish `habs : |((discr K : ℤ) : ℝ)| = (l : ℝ)`. Rewrite using `[hd]`.

Use `push_cast`. Conclude with `abs_of_pos hl0`. Rewrite `h` using `[hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one]`. Establish `hx0 : 0 < Real.sqrt (l : ℝ)` using `Real.sqrt_pos.mpr hl0`. Establish `h5r : (5 : ℝ) ≤ l` using `by exact_mod_cast h5`.

Establish `hx1 : Real.sqrt (l : ℝ) ≠ 1`. Introduce `h1`. Establish `hs` using `Real.sq_sqrt hl0.le`. Rewrite `hs` using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog` using `Real.log_lt_sub_one_of_pos hx0 hx1`. Establish `hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l` using `Real.mul_self_sqrt hl0.le`. Establish `hlt : (classNumber K : ℝ) < l`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_lt_mul_of_pos_left _ hx0` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = l := hsq`. Conclude with `hlt` after adjusting the coercions.
-/
theorem UpperTheory.V.X.hQuad :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ), l.Prime → 5 ≤ l → Module.finrank ℚ K = 2 → discr K = l → classNumber K < l := by
  intro K _ _ l hl h5 hn hd
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have habs : |((discr K : ℤ) : ℝ)| = (l : ℝ) := by
    rw [hd]
    push_cast
    exact abs_of_pos hl0
  rw [hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have hx0 : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hl0
  have h5r : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hx1 : Real.sqrt (l : ℝ) ≠ 1 := by
    intro h1
    have hs := Real.sq_sqrt hl0.le
    rw [h1] at hs
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hx0 hx1
  have hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l := Real.mul_self_sqrt hl0.le
  have hlt : (classNumber K : ℝ) < l := by
    calc (classNumber K : ℝ) ≤ Real.sqrt (l : ℝ) * (1 + Real.log (Real.sqrt (l : ℝ))) := h
      _ < Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hx0
        linarith
      _ = l := hsq
  exact_mod_cast hlt
