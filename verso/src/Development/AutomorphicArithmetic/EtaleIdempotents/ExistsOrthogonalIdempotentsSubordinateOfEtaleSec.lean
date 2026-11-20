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
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
