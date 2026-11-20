import Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy

open CategoryTheory Limits GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ K L I _ f _`. Establish `hI` using `CochainComplex.IsKInjective.rightOrthogonal I`. Rewrite `hI` using `[← ObjectProperty.isLocal_trW]`. Establish `hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f)`. Rewrite using `[← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]`.

Conclude with `(HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance`. Establish `hb` using `hI _ hf`. Use `⟨fun a => ?_, fun m m' h => ?_⟩` and prove the remaining obligations. Take `⟨m', hm'⟩` from `hb.2 ((HomotopyCategory.quotient _ _).map a)`. Take `⟨m, rfl⟩` from `(HomotopyCategory.quotient _ _).map_surjective m'`.

Use `⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp]`. Conclude with `hm'`. Take `⟨h⟩` from `h`. Establish `e` using `HomotopyCategory.eq_of_homotopy _ _ h`.

Rewrite `e` using `[Functor.map_comp, Functor.map_comp]`. Conclude with `⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩`.
-/
theorem LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  intro R _ K L I _ f _
  have hI := CochainComplex.IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  have hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance
  have hb := hI _ hf
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m', hm'⟩ := hb.2 ((HomotopyCategory.quotient _ _).map a)
    obtain ⟨m, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective m'
    refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_comp]; exact hm'
  · obtain ⟨h⟩ := h
    have e := HomotopyCategory.eq_of_homotopy _ _ h
    rw [Functor.map_comp, Functor.map_comp] at e
    exact ⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩
