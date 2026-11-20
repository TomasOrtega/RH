import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Unfold `CycloDistStatement`. Introduce `O _ _ l s hl hlm`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `hE` using `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (p := l) s`. Establish `hXmon : (Polynomial.X + 1 : Polynomial ℤ).Monic`.

Simplify using `using Polynomial.monic_X_add_C (1 : ℤ)`. Establish `hXdeg : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≠ 0`. Rewrite using `[← Polynomial.C_1, Polynomial.natDegree_X_add_C]`. Conclude with `one_ne_zero`. Establish `hPmon : ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).Monic` using `(Polynomial.cyclotomic.monic _ ℤ).comp hXmon hXdeg`.

Establish `hQ : (Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) = ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).map (Int.castRingHom O)`. Simplify using `[Polynomial.map_comp]`. Rewrite using `[hQ]`. Use `{ mem := fun {n} hn => ?_, monic := hPmon.map _ }` and prove the remaining obligations. Rewrite `hn` using `[hPmon.natDegree_map]`.

Rewrite using `[Polynomial.coeff_map]`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp (hE.mem hn)`. Rewrite using `[← ha, smul_eq_mul, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (by simpa using hlm)`.
-/
theorem cycloDist : CycloDistStatement := by
  unfold CycloDistStatement
  intro O _ _ l s hl hlm
  haveI : Fact l.Prime := ⟨hl⟩
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (p := l) s
  have hXmon : (Polynomial.X + 1 : Polynomial ℤ).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ℤ)
  have hXdeg : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≠ 0 := by
    rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]; exact one_ne_zero
  have hPmon : ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).Monic :=
    (Polynomial.cyclotomic.monic _ ℤ).comp hXmon hXdeg
  have hQ : (Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) =
      ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).map (Int.castRingHom O) := by
    simp [Polynomial.map_comp]
  rw [hQ]
  refine { mem := fun {n} hn => ?_, monic := hPmon.map _ }
  rw [hPmon.natDegree_map] at hn
  rw [Polynomial.coeff_map]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
  rw [← ha, smul_eq_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (by simpa using hlm)

end LevelStatements.Lv
