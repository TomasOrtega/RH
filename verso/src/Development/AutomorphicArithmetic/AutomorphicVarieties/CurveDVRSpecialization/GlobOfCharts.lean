import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

open IsLocalRing in
/- English proof (translation)
Introduce `X _ M hTI hG x R _ _ _ f hC L hLT hLG hConcl`. Establish `eG : ∀ P, P ∈ L.Good ↔ f P ∈ M.Good` using `fun P => by rw [hLG]; rfl`. Establish `eT : ∀ P, P ∈ L.TI ↔ f P ∈ M.TI` using `fun P => by rw [hLT]; rfl`. Establish `hsub : ∀ P : PrimeSpectrum R, f P ∈ M.Good → closure {f P} ⊆ M.Good` using `fun P h => hG.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)`. Establish `hmeet : ∀ P : PrimeSpectrum R, (closure {f P} ∩ M.TI).Nonempty → f P ∈ M.TI`.

Introduce and unpack `P ⟨y, hy, hyT⟩`. Take `⟨z, hzT, hz⟩` from `mem_closure_iff.mp hy _ hTI hyT`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Rewrite using `[← hz]`. Conclude with `hzT`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hD Y Y' hY hY' hxY hxY' hYg`. Take `⟨P, hPm, rfl⟩` from `hC.onto Y hY.1 hxY`. Take `⟨P', hP'm, rfl⟩` from `hC.onto Y' hY'.1 hxY'`. Establish `hPG : P ∈ L.Good` using `(eG P).mpr (hYg (subset_closure (Set.mem_singleton _)))`.

Establish `hPT : P ∈ L.TI` using `(eT P).mpr (hmeet P hY.2)`. Establish `h'` using `hConcl P hPG hPT (hD P hPm) P' ((eT P').mpr (hmeet P' hY'.2)) hP'm`. Conclude with `hsub P' ((eG P').mp h')`. Introduce `hall`. Use `⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩, mem_irreducibleComponent⟩` and prove the remaining obligations.

Take `⟨P, hPm, hPY⟩` from `hC.onto _ (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent`. Use `⟨f P, ?_, (eT P).mp (hall P hPm)⟩` and prove the remaining obligations. Rewrite using `[← hPY]`. Conclude with `subset_closure (Set.mem_singleton _)`. Introduce and unpack `⟨I, hIG, hIT, hID⟩`.

Take `⟨p, hpm, hpI⟩` from `Ideal.exists_minimalPrimes_le (J := I.asIdeal) (bot_le : (⊥ : Ideal R) ≤ I.asIdeal)`. Use `haveI hpp : p.IsPrime := hpm.1.1`. Set `P : PrimeSpectrum R` to `⟨p, hpp⟩`. Establish `hPmin : P.asIdeal ∈ minimalPrimes R` using `hpm`. Establish `hopen : IsOpen L.TI`.

Rewrite using `[hLT]`. Conclude with `hTI.preimage hC.cont`. Establish `hPT : P ∈ L.TI`. Establish `hcl : I ∈ closure ({P} : Set (PrimeSpectrum R))` using `(PrimeSpectrum.le_iff_mem_closure P I).mp hpI`. Take `⟨z, hzT, hz⟩` from `mem_closure_iff.mp hcl _ hopen hIT`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Rewrite using `[← hz]`. Conclude with `hzT`. Establish `hPG` using `hConcl I hIG hIT hID P hPT hPmin`. Conclude with `⟨closure {f P}, ⟨hC.min P hPmin, f P, subset_closure (Set.mem_singleton _), (eT P).mp hPT⟩, hsub P ((eG P).mp hPG)⟩`.
-/
theorem UpperTheory.V.Pr.globOfCharts :
    UpperTheory.V.Pr.GlobOfCharts := by
  intro X _ M hTI hG x R _ _ _ f hC L hLT hLG hConcl
  have eG : ∀ P, P ∈ L.Good ↔ f P ∈ M.Good := fun P => by rw [hLG]; rfl
  have eT : ∀ P, P ∈ L.TI ↔ f P ∈ M.TI := fun P => by rw [hLT]; rfl
  have hsub : ∀ P : PrimeSpectrum R, f P ∈ M.Good → closure {f P} ⊆ M.Good :=
    fun P h => hG.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have hmeet : ∀ P : PrimeSpectrum R, (closure {f P} ∩ M.TI).Nonempty → f P ∈ M.TI := by
    rintro P ⟨y, hy, hyT⟩
    obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hy _ hTI hyT
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzT
  refine ⟨?_, ?_, ?_⟩
  · intro hD Y Y' hY hY' hxY hxY' hYg
    obtain ⟨P, hPm, rfl⟩ := hC.onto Y hY.1 hxY
    obtain ⟨P', hP'm, rfl⟩ := hC.onto Y' hY'.1 hxY'
    have hPG : P ∈ L.Good := (eG P).mpr (hYg (subset_closure (Set.mem_singleton _)))
    have hPT : P ∈ L.TI := (eT P).mpr (hmeet P hY.2)
    have h' := hConcl P hPG hPT (hD P hPm) P' ((eT P').mpr (hmeet P' hY'.2)) hP'm
    exact hsub P' ((eG P').mp h')
  · intro hall
    refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
      mem_irreducibleComponent⟩
    obtain ⟨P, hPm, hPY⟩ :=
      hC.onto _ (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent
    refine ⟨f P, ?_, (eT P).mp (hall P hPm)⟩
    rw [← hPY]
    exact subset_closure (Set.mem_singleton _)
  · rintro ⟨I, hIG, hIT, hID⟩
    obtain ⟨p, hpm, hpI⟩ :=
      Ideal.exists_minimalPrimes_le (J := I.asIdeal) (bot_le : (⊥ : Ideal R) ≤ I.asIdeal)
    haveI hpp : p.IsPrime := hpm.1.1
    let P : PrimeSpectrum R := ⟨p, hpp⟩
    have hPmin : P.asIdeal ∈ minimalPrimes R := hpm
    have hopen : IsOpen L.TI := by
      rw [hLT]
      exact hTI.preimage hC.cont
    have hPT : P ∈ L.TI := by
      have hcl : I ∈ closure ({P} : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.le_iff_mem_closure P I).mp hpI
      obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hcl _ hopen hIT
      rw [Set.mem_singleton_iff] at hz
      rw [← hz]
      exact hzT
    have hPG := hConcl I hIG hIT hID P hPT hPmin
    exact ⟨closure {f P}, ⟨hC.min P hPmin, f P, subset_closure (Set.mem_singleton _), (eT P).mp hPT⟩,
      hsub P ((eG P).mp hPG)⟩
