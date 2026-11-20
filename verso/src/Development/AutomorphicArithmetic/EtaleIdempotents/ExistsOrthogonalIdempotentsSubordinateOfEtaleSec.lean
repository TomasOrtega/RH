import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Set `A : I → CommRingCat.{0}` to `fun k => CommRingCat.of (Localization.Away (f k))`. Set `m : ∀ k, Spec (A k) ⟶ Spec (CommRingCat.of R)` to `fun k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))`. Set `g : ∐ (fun k => Spec (A k)) ⟶ Spec (CommRingCat.of R)` to `Sigma.desc m`. Establish `hEt : Etale g`. Use `(IsZariskiLocalAtSource.sigmaDesc (P := @Etale) ?_)` and prove the remaining obligations.

Introduce `k`. Use `infer_instance`. Establish `hSu : Surjective g`. Use `⟨fun p => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hcov p`.

Establish `hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f k))))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away (f k)) (f k)]`. Conclude with `hk`. Take `⟨q, rfl⟩` from `hp`. Use `⟨(Sigma.ι (fun k => Spec (A k)) k) q, ?_⟩` and prove the remaining obligations.

Establish `: Sigma.ι (fun k => Spec (A k)) k ≫ g = m k` using `Sigma.ι_desc _ _`. Rewrite using `[← Scheme.Hom.comp_apply, this]`. Both sides reduce to the same expression. Take `⟨s, hs⟩` from `hsec _ g hEt hSu`. Establish `hg : g = sigmaSpec A ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k))))`.

Use `Sigma.hom_ext _ _ fun k => ?_` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `r'` to `Spec.preimage (s ≫ sigmaSpec A)`. Establish `hr' : Spec.map r' = s ≫ sigmaSpec A` using `Spec.map_preimage _`.

Establish `hc : CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k))) ≫ r' = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hr', Category.assoc, ← hg, hs, Spec.map_id]`. Conclude with `⟨r'.hom, congrArg CommRingCat.Hom.hom hc⟩`.
-/
private lemma key {R : Type} [CommRing R]
    (hsec : ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f →
      ∃ s, s ≫ f = 𝟙 _)
    {I : Type} [Finite I] (f : I → R) (hcov : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal) :
    ∃ r : (Π k, Localization.Away (f k)) →+* R,
      r.comp (algebraMap R (Π k, Localization.Away (f k))) = RingHom.id R := by
  let A : I → CommRingCat.{0} := fun k => CommRingCat.of (Localization.Away (f k))
  let m : ∀ k, Spec (A k) ⟶ Spec (CommRingCat.of R) :=
    fun k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))
  let g : ∐ (fun k => Spec (A k)) ⟶ Spec (CommRingCat.of R) := Sigma.desc m
  have hEt : Etale g := by
    refine (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) ?_)
    intro k
    infer_instance
  have hSu : Surjective g := by
    refine ⟨fun p => ?_⟩
    obtain ⟨k, hk⟩ := hcov p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f k)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f k)) (f k)]
      exact hk
    obtain ⟨q, rfl⟩ := hp
    refine ⟨(Sigma.ι (fun k => Spec (A k)) k) q, ?_⟩
    have : Sigma.ι (fun k => Spec (A k)) k ≫ g = m k := Sigma.ι_desc _ _
    rw [← Scheme.Hom.comp_apply, this]
    rfl
  obtain ⟨s, hs⟩ := hsec _ g hEt hSu
  have hg : g = sigmaSpec A ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k)))) := by
    refine Sigma.hom_ext _ _ fun k => ?_
    rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  let r' := Spec.preimage (s ≫ sigmaSpec A)
  have hr' : Spec.map r' = s ≫ sigmaSpec A := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k))) ≫ r' = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr', Category.assoc, ← hg, hs, Spec.map_id]
  exact ⟨r'.hom, congrArg CommRingCat.Hom.hom hc⟩

/- English proof (translation)
Introduce `R _ hsec ι W hWo hWc`. Set `J : Type` to `{x : ι × R // (PrimeSpectrum.basicOpen x.2 : Set (PrimeSpectrum R)) ⊆ W x.1}`. Establish `hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆ ⋃ j : J, (PrimeSpectrum.basicOpen j.1.2 : Set (PrimeSpectrum R))`. Introduce `p _`. Take `⟨i, hi⟩` from `hWc p`.

Take `⟨_, ⟨f, rfl⟩, hpf, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (hWo i)`. Conclude with `Set.mem_iUnion.2 ⟨⟨(i, f), hsub⟩, hpf⟩`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover _ (fun j : J => (PrimeSpectrum.basicOpen j.1.2).isOpen) hcov`. Set `f : t → R` to `fun k => k.1.1.2`. Establish `hcovI : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal`.

Introduce `p`. Take `⟨j, hj, hp⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ p))`. Conclude with `⟨⟨j, hj⟩, hp⟩`. Take `⟨r, hr⟩` from `key hsec f hcovI`. Establish `hrf : ∀ x, r (algebraMap R _ x) = x` using `fun x => congrArg (fun h => h x) hr`.

Use `⟨t, inferInstance, fun k => r (Pi.single k 1), fun k => k.1.1.1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(CompleteOrthogonalIdempotents.single (fun k => Localization.Away (f k))).map r`. Introduce `k p hp`. Use `k.1.2 ?_` and prove the remaining obligations. Use `show f k ∉ p.asIdeal`.

Introduce `hf`. Apply `hp` to reduce the goal to its premises. Establish `hu : Pi.single k 1 = algebraMap R (Π k, Localization.Away (f k)) (f k) * Pi.single k (IsLocalization.Away.invSelf (f k))`. Use extensionality with `l`. Distinguish the cases in `h : l = k`.

Substitute `h` using the available equality. Simplify using `[IsLocalization.Away.mul_invSelf]`. Simplify using `[Pi.single_eq_of_ne h]`. Use `show r (Pi.single k 1) ∈ p.asIdeal`. Rewrite using `[hu, map_mul, hrf]`.

Conclude with `p.asIdeal.mul_mem_right _ hf`.
-/
theorem UpperTheory.exists_orthogonalIdempotents_subordinate_of_etale_sections :
    ∀ (R : Type) [CommRing R],
        (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
        ∀ (ι : Type) (W : ι → Set (PrimeSpectrum R)), (∀ i, IsOpen (W i)) → (∀ p, ∃ i, p ∈ W i) →
        ∃ (I : Type) (_ : Fintype I) (e : I → R) (a : I → ι), CompleteOrthogonalIdempotents e ∧
          ∀ i (p : PrimeSpectrum R), e i ∉ p.asIdeal → p ∈ W (a i) := by
  intro R _ hsec ι W hWo hWc
  classical
  let J : Type := {x : ι × R // (PrimeSpectrum.basicOpen x.2 : Set (PrimeSpectrum R)) ⊆ W x.1}
  have hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ j : J, (PrimeSpectrum.basicOpen j.1.2 : Set (PrimeSpectrum R)) := by
    intro p _
    obtain ⟨i, hi⟩ := hWc p
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (hWo i)
    exact Set.mem_iUnion.2 ⟨⟨(i, f), hsub⟩, hpf⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun j : J => (PrimeSpectrum.basicOpen j.1.2).isOpen) hcov
  let f : t → R := fun k => k.1.1.2
  have hcovI : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal := by
    intro p
    obtain ⟨j, hj, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
    exact ⟨⟨j, hj⟩, hp⟩
  obtain ⟨r, hr⟩ := key hsec f hcovI
  have hrf : ∀ x, r (algebraMap R _ x) = x := fun x => congrArg (fun h => h x) hr
  refine ⟨t, inferInstance, fun k => r (Pi.single k 1), fun k => k.1.1.1, ?_, ?_⟩
  · exact (CompleteOrthogonalIdempotents.single (fun k => Localization.Away (f k))).map r
  · intro k p hp
    refine k.1.2 ?_
    show f k ∉ p.asIdeal
    intro hf
    apply hp
    have hu : Pi.single k 1 = algebraMap R (Π k, Localization.Away (f k)) (f k) *
        Pi.single k (IsLocalization.Away.invSelf (f k)) := by
      ext l
      by_cases h : l = k
      · subst h
        simp [IsLocalization.Away.mul_invSelf]
      · simp [Pi.single_eq_of_ne h]
    show r (Pi.single k 1) ∈ p.asIdeal
    rw [hu, map_mul, hrf]
    exact p.asIdeal.mul_mem_right _ hf
