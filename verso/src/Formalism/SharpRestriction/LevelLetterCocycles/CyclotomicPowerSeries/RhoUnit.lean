import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Use `first`. Consider the case `(have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by`. Rewrite using `[PowerSeries.smul_eq_C_mul, mul_one]`. Rewrite using `[e, map_smul, map_one, ← algebraMap_smul S c (1 : PowerSeries S), PowerSeries.smul_eq_C_mul, mul_one, PowerSeries.constantCoeff_C])`. Consider the case `(have e : (C c : PowerSeries O) = algebraMap O (PowerSeries O) c := by first`.

Consider the case `rfl`. Consider the case `simp [PowerSeries.algebraMap_eq]`. Consider the case `exact (PowerSeries.algebraMap_apply' c).symm`. Rewrite using `[e, ρ.commutes]`. Use `first`.

Consider the case `simp`. Consider the case `(rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)`. Consider the case `simp [PowerSeries.algebraMap_apply'])`.
-/
private theorem constantCoeff_algHom_C_eq_algebraMap {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (ρ : PowerSeries O →ₐ[O] PowerSeries S) (c : O) :
    constantCoeff (ρ (C c)) = algebraMap O S c := by
  first
  | (have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by
       rw [PowerSeries.smul_eq_C_mul, mul_one]
     rw [e, map_smul, map_one, ← algebraMap_smul S c (1 : PowerSeries S),
       PowerSeries.smul_eq_C_mul, mul_one, PowerSeries.constantCoeff_C])
  | (have e : (C c : PowerSeries O) = algebraMap O (PowerSeries O) c := by
       first
       | rfl
       | simp [PowerSeries.algebraMap_eq]
       | exact (PowerSeries.algebraMap_apply' c).symm
     rw [e, ρ.commutes]
     first
     | simp
     | (rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)
     | simp [PowerSeries.algebraMap_apply'])

/- English proof (translation)
Use `first`. Consider the case `exact PowerSeries.isUnit_iff_constantCoeff.mpr h`. Consider the case `(obtain ⟨u, hu⟩ := h`. Conclude with `isUnit_of_mul_eq_one _ _ (PowerSeries.mul_invOfUnit f u hu.symm))`.
-/
private theorem isUnit_of_isUnit_constantCoeff {S : Type} [CommRing S] {f : PowerSeries S}
    (h : IsUnit (constantCoeff f)) : IsUnit f := by
  first
  | exact PowerSeries.isUnit_iff_constantCoeff.mpr h
  | (obtain ⟨u, hu⟩ := h
     exact isUnit_of_mul_eq_one _ _ (PowerSeries.mul_invOfUnit f u hu.symm))

/- English proof (translation)
Unfold `RhoUnitStatement`. Introduce `O S _ _ _ ρ p a c hp hc hmem`. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.mp hmem`. Establish `h2 : constantCoeff (ρ v) * constantCoeff (ρ a) = algebraMap O S c`. Rewrite using `[← constantCoeff_algHom_C_eq_algebraMap ρ c, ← huv]`.

Simplify using `only [map_add, map_mul, hp, mul_zero, zero_add]`. Rewrite `hc` using `[← h2]`. Conclude with `isUnit_of_isUnit_constantCoeff (IsUnit.mul_iff.mp hc).2`.
-/
theorem rhoUnit : RhoUnitStatement := by
  unfold RhoUnitStatement
  intro O S _ _ _ ρ p a c hp hc hmem
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hmem
  have h2 : constantCoeff (ρ v) * constantCoeff (ρ a) = algebraMap O S c := by
    rw [← constantCoeff_algHom_C_eq_algebraMap ρ c, ← huv]
    simp only [map_add, map_mul, hp, mul_zero, zero_add]
  rw [← h2] at hc
  exact isUnit_of_isUnit_constantCoeff (IsUnit.mul_iff.mp hc).2

end LevelStatements.Lv
