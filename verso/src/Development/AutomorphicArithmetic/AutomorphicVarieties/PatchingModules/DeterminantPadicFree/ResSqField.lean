import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Use `letI := (PowerSeries.map (algebraMap K K')).toAlgebra`. Set `b` to `Module.finBasis K K'`. Use `show Module.Finite (PowerSeries K) (PowerSeries K')`. Use `⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `φ _`. Establish `key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) • PowerSeries.C (b i)`. Use extensionality with `n`. Simplify using `only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Repeatedly rewrite using `[← Algebra.smul_def]`.

Conclude with `(b.sum_repr _).symm`. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Pa.Det.resSq_fin {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [Module.Finite K K'] : (PowerSeries.map (algebraMap K K')).Finite := by
  classical
  letI := (PowerSeries.map (algebraMap K K')).toAlgebra
  let b := Module.finBasis K K'
  show Module.Finite (PowerSeries K) (PowerSeries K')
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simp_rw [← Algebra.smul_def]
    exact (b.sum_repr _).symm
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

/- English proof (translation)
Use `letI := Fintype.ofFinite K`. Set `p : Polynomial K` to `∏ a : K, (Polynomial.X ^ 2 - Polynomial.C a)`. Establish `hp : p ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun a _ => Polynomial.X_pow_sub_C_ne_zero (by norm_num) a`. Use `⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun a => ?_⟩` and prove the remaining obligations. Establish `hs` using `Polynomial.SplittingField.splits p`.

Establish `hd : (Polynomial.X ^ 2 - Polynomial.C a) ∣ p` using `Finset.dvd_prod_of_mem _ (Finset.mem_univ a)`. Establish `hs' : ((Polynomial.X ^ 2 - Polynomial.C a).map (algebraMap K p.SplittingField)).Splits` using `hs.of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hd)`. Take `⟨x, hx⟩` from `hs'.exists_eval_eq_zero (by`. Rewrite using `[Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx`. Rewrite using `[← sq]`. Conclude with `(sub_eq_zero.mp hx).symm`.
-/
private theorem UpperTheory.V.Pa.Det.resSq_field (K : Type) [Field K] [Finite K] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K'),
      ∀ a : K, IsSquare (algebraMap K K' a) := by
  classical
  letI := Fintype.ofFinite K
  let p : Polynomial K := ∏ a : K, (Polynomial.X ^ 2 - Polynomial.C a)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) a
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  have hs := Polynomial.SplittingField.splits p
  have hd : (Polynomial.X ^ 2 - Polynomial.C a) ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
  have hs' : ((Polynomial.X ^ 2 - Polynomial.C a).map (algebraMap K p.SplittingField)).Splits :=
    hs.of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hd)
  obtain ⟨x, hx⟩ := hs'.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  refine ⟨x, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
  rw [← sq]; exact (sub_eq_zero.mp hx).symm

/- English proof (translation)
Introduce `K _ _`. Take `⟨K', _, _, _, hsq⟩` from `UpperTheory.V.Pa.Det.resSq_field K`. Use `haveI : Finite K' := Module.finite_of_finite K`. Establish `hcc : ∀ φ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map (algebraMap K K') φ) = algebraMap K K' (PowerSeries.constantCoeff φ)`. Introduce `φ`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Use `⟨K', inferInstance, inferInstance, PowerSeries.map (algebraMap K K'), PowerSeries.map_injective _ (algebraMap K K').injective, ⟨fun φ hφ => ?_⟩, UpperTheory.V.Pa.Det.resSq_fin, fun c => ?_⟩` and prove the remaining obligations. Rewrite `hφ` using `[PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero, map_ne_zero_iff _ (algebraMap K K').injective]`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]`. Conclude with `hφ`.

Take `⟨r, hr⟩` from `hsq (PowerSeries.constantCoeff (c : PowerSeries K))`. Use `⟨residue (PowerSeries K') (PowerSeries.C r), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, hcc, hr, map_mul, PowerSeries.constantCoeff_C, sub_self]`. Conclude with `not_isUnit_zero`.
-/
theorem UpperTheory.V.Pa.Det.resSq :
    ∀ {K : Type} [Field K] [Finite K], ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : PowerSeries K →+* PowerSeries K'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j c)) := by
  intro K _ _
  obtain ⟨K', _, _, _, hsq⟩ := UpperTheory.V.Pa.Det.resSq_field K
  haveI : Finite K' := Module.finite_of_finite K
  have hcc : ∀ φ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map (algebraMap K K') φ) =
      algebraMap K K' (PowerSeries.constantCoeff φ) := by
    intro φ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine ⟨K', inferInstance, inferInstance, PowerSeries.map (algebraMap K K'),
    PowerSeries.map_injective _ (algebraMap K K').injective, ⟨fun φ hφ => ?_⟩,
    UpperTheory.V.Pa.Det.resSq_fin, fun c => ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ (algebraMap K K').injective] at hφ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hφ
  · obtain ⟨r, hr⟩ := hsq (PowerSeries.constantCoeff (c : PowerSeries K))
    refine ⟨residue (PowerSeries K') (PowerSeries.C r), ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, hcc, hr, map_mul,
      PowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
