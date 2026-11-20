import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem co_mvps_fin (R : Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance
  | succ n ih =>
    exact co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm
      (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Alg.co_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ], IsCO O (MvPowerSeries σ R) := by
  intro O _ _ R _ _ hR σ _
  have hc : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherian := MvPowerSeries.isNoetherianRing R
      complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n)
      isLocalHom := ⟨fun a ha => ?_⟩
      res_surj := fun x => ?_ }
  · have h := isUnit_constantCoeff _ ha
    rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] at h
    exact IsLocalHom.map_nonunit a h
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (constantCoeff x)
    refine ⟨a, fun h => ha ?_⟩
    have h2 := isUnit_constantCoeff _ h
    rwa [map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C] at h2
