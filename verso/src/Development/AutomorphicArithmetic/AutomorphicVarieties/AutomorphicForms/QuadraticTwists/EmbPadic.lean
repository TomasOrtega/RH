import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `K _ _ hK l _ hι j x`. Take `⟨ι⟩` from `hι`. Establish `hint : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Establish `hmon : (minpoly ℚ x).Monic` using `minpoly.monic hint`. Establish `hdle : (minpoly ℚ x).natDegree ≤ 2` using `hK ▸ minpoly.natDegree_le x`.

Establish `hdpos : 0 < (minpoly ℚ x).natDegree` using `minpoly.natDegree_pos hint`. Establish `hroot : ∀ f : K →+* Om l, Polynomial.aeval (f x) (minpoly ℚ x) = 0`. Introduce `f`. Rewrite using `[show f x = f.toRatAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hy` using `hroot j`.

Establish `hw` using `hroot ((algebraMap ℚ_[l] (Om l)).comp ι)`. Establish `hlead : (minpoly ℚ x).coeff (minpoly ℚ x).natDegree = 1` using `hmon`. Rewrite `hy`, `hw` using `[Polynomial.aeval_eq_sum_range]`. Take `hd | hd : (minpoly ℚ x).natDegree = 1 ∨ (minpoly ℚ x).natDegree = 2` from `by omega`. Rewrite `hy`, `hlead` using `[hd]`.

Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one, mul_one, zero_add, hlead, Rat.cast_one, one_mul] at hy`. Use `⟨-((minpoly ℚ x).coeff 0 : ℚ_[l]), ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, map_ratCast]`. Take the linear combination `-hy`. Rewrite `hy`, `hw`, `hlead` using `[hd]`.

Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one, mul_one, zero_add, hlead, Rat.cast_one, one_mul, RingHom.comp_apply] at hy hw`. Establish `hfac : (j x - algebraMap ℚ_[l] (Om l) (ι x)) * (j x + algebraMap ℚ_[l] (Om l) (ι x) + ((minpoly ℚ x).coeff 1 : Om l)) = 0`. Take the linear combination `hy - hw`. Break down `mul_eq_zero.1 hfac with h | h` into its components or cases. Conclude with `⟨ι x, (sub_eq_zero.1 h).symm⟩`.

Use `⟨-(ι x) - ((minpoly ℚ x).coeff 1 : ℚ_[l]), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_neg, map_ratCast]`. Take the linear combination `-h`.
-/
theorem UpperTheory.V.Af.Cq.embPadic :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], Nonempty (K →+* ℚ_[l]) → ∀ (j : K →+* Om l) (x : K),
        j x ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro K _ _ hK l _ hι j x
  obtain ⟨ι⟩ := hι
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
  have hdle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hdpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hroot : ∀ f : K →+* Om l, Polynomial.aeval (f x) (minpoly ℚ x) = 0 := by
    intro f
    rw [show f x = f.toRatAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hy := hroot j
  have hw := hroot ((algebraMap ℚ_[l] (Om l)).comp ι)
  have hlead : (minpoly ℚ x).coeff (minpoly ℚ x).natDegree = 1 := hmon
  rw [Polynomial.aeval_eq_sum_range] at hy hw
  obtain hd | hd : (minpoly ℚ x).natDegree = 1 ∨ (minpoly ℚ x).natDegree = 2 := by omega
  · rw [hd] at hy hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul] at hy
    refine ⟨-((minpoly ℚ x).coeff 0 : ℚ_[l]), ?_⟩
    rw [map_neg, map_ratCast]
    linear_combination -hy
  · rw [hd] at hy hw hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul, RingHom.comp_apply] at hy hw
    have hfac : (j x - algebraMap ℚ_[l] (Om l) (ι x)) *
        (j x + algebraMap ℚ_[l] (Om l) (ι x) + ((minpoly ℚ x).coeff 1 : Om l)) = 0 := by
      linear_combination hy - hw
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨ι x, (sub_eq_zero.1 h).symm⟩
    · refine ⟨-(ι x) - ((minpoly ℚ x).coeff 1 : ℚ_[l]), ?_⟩
      rw [map_sub, map_neg, map_ratCast]
      linear_combination -h
