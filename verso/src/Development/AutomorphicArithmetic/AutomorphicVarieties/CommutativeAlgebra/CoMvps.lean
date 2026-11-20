import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Rewrite using `[← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]`. Conclude with `h`.
-/
private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance`. Consider the case `succ n ih`. Conclude with `co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))`.
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
Introduce `O _ _ R _ _ hR σ _`. Establish `hc : IsAdicComplete (maximalIdeal R) R` using `IsCO.complete (O := O)`. Establish `hl : IsLocalHom (algebraMap O R)` using `IsCO.isLocalHom`. Establish `hn : IsNoetherianRing R` using `hR.toIsNoetherian`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin σ`.

Use `{ toIsLocalRing := inferInstance toIsNoetherian := MvPowerSeries.isNoetherianRing R complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n) isLocalHom := ⟨fun a ha => ?_⟩ res_surj := fun x => ?_ }` and prove the remaining obligations. Establish `h` using `isUnit_constantCoeff _ ha`. Rewrite `h` using `[MvPowerSeries.algebraMap_apply, constantCoeff_C]`. Conclude with `IsLocalHom.map_nonunit a h`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) (constantCoeff x)`.

Use `⟨a, fun h => ha ?_⟩` and prove the remaining obligations. Establish `h2` using `isUnit_constantCoeff _ h`. Rewrite `h2` using `[map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]`. Then use the resulting hypothesis.
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
