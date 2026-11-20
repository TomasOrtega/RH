import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.UpCycOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT

/- English proof (translation)
Take `⟨M, hM, hle⟩` from `(eq_top_or_exists_le_coatom (commutator Γ)).resolve_left (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne`. Establish `hn : M.Normal` using `⟨fun n hn g => by`. Establish `h1 : g * n * g⁻¹ * n⁻¹ ∈ M` using `hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))`. Simplify using `using M.mul_mem h1 hn⟩`. Use `⟨M, hn, ?_⟩` and prove the remaining obligations.

Take `⟨p, hp, hd⟩` from `Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)`. Use `haveI := Fact.mk hp`. Take `⟨g, hg⟩` from `exists_prime_orderOf_dvd_card' p hd`. Establish `h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤`. Use `hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)` and prove the remaining obligations.

Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]`. Conclude with `one_mem _`. Take `⟨x, rfl⟩` from `QuotientGroup.mk'_surjective M g`. Establish `hx : x ∈ M` using `e ▸ Subgroup.mem_zpowers _`. Rewrite `hg` using `[QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one]`.

Conclude with `hp.one_lt.ne hg`. Establish `h2 : Subgroup.zpowers g = ⊤` using `Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)`. Rewrite using `[Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]`. Conclude with `hp`.
-/
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

/- English proof (translation)
The claim follows from `{ isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }`.
-/
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }

/- English proof (translation)
Take `⟨π, hreg, -, hat⟩` from `ha`. Set `j : E ≃+* F` to `(RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm`. Use `⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg, (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw`. Take `⟨B, hB, hF⟩` from `hw`.

Establish `hu : w.under (𝓞 F) = plMap j w` using `HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)`. Establish `hn : normV w = normV (plMap j w)` using `(absNorm_plMap j w).symm`. Use `⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩` and prove the remaining obligations. Establish `h3` using `(UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)`. Rewrite using `[hn, ← hu]`.

Simplify using `only [pow_one, Multiset.map_id'] at h3`. Conclude with `h3`.
-/
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (ha : IsAutC ι r) (hi : IsIrr (r.comp (galEmb F E Ω))) :
    IsAutC ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, -, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
