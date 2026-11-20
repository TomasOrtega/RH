import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Slopes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB`. Take `⟨hinf, hdual, -⟩` from `hπ`. Establish `hic : ∀ τ, (CG.mk π).infChar τ = infOf m` using `fun τ => CG.HasInfChar.infChar_eq (hinf τ)`. Establish `hreg : (CG.mk π).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[hic]`.

Use `⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `add_left_cancel e` after adjusting the coercions. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hz`. Conclude with `⟨m i, add_comm _ _⟩`. Establish `hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n)` using `⟨fun v => by rw [locInf_pow, quadChar_locInf], by`.

Rewrite using `[map_pow, compNorm_quadChar, one_pow]`. Conclude with `(GlobalTheory.ContraPair.dualIsConjBy_one π).2 hdual⟩`. Take `⟨⟨σ, hσ⟩, hiso⟩` from `locCompC hP K n π w`. Establish `hBσ` using `((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB`. Use `slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_` and prove the remaining obligations.

Take `⟨r, wt, HT, H⟩` from `hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol`. Establish `hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i` using `fun τ => by`. Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun i _ => by simp`.

Use `⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Establish `a` using `H.above _ _ (Loc.tiedP l) w A h O Bw hj`. Conclude with `⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩`.
-/
theorem UpperTheory.V.Af.intK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, hdual, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hdual⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
