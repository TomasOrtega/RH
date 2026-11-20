import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.cl_norm0 :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] [IsDomain R], IsCL O R → ringKrullDim R = 1 → Function.Injective (algebraMap O R) → Module.Finite O R := by
  intro O _ _ _ _ R _ _ _ _ hcl hdim hinj
  obtain ⟨d, φ, -, hφ, -, hd⟩ := (UpperTheory.V.CA.cl_nn O R hcl).1 hinj
  rw [hdim] at hd
  have hd1 : d + 1 = 1 := by exact_mod_cast hd.symm
  obtain rfl : d = 0 := by omega
  have hsurj : Function.Surjective (algebraMap O (MvPowerSeries (Fin 0) O)) := by
    intro g
    refine ⟨MvPowerSeries.constantCoeff g, ?_⟩
    ext n
    obtain rfl : n = 0 := Subsingleton.elim _ _
    simp [MvPowerSeries.algebraMap_apply]
  have hcomp : algebraMap O R = (φ : MvPowerSeries (Fin 0) O →+* R).comp (algebraMap O (MvPowerSeries (Fin 0) O)) := by
    ext x
    simp
  have hfin : (algebraMap O R).Finite := by
    rw [hcomp]
    exact RingHom.Finite.comp hφ (RingHom.Finite.of_surjective _ hsurj)
  exact RingHom.finite_algebraMap.mp hfin
