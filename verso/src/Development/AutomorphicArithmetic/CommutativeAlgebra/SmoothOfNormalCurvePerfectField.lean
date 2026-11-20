import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace UpperTheory.LocallyOfRingHomAway

/- English proof (translation)
Establish `hnoeth : IsNoetherianRing R` using `Algebra.FiniteType.isNoetherianRing Ω R`. Establish `hkd : Ring.KrullDimLE 1 R`. Rewrite using `[Ring.krullDimLE_iff]`. Conclude with `hdim` after adjusting the coercions. Establish `hdl : Ring.DimensionLEOne R` using `⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩`.

Establish `hded : IsDedekindDomain R` using `{ }`. Establish `hmbot : m ≠ ⊥`. Introduce `h`. Apply `hnf` to reduce the goal to its premises. Rewrite using `[Ring.isField_iff_maximal_bot]`.

Rewrite using `[← h]`. Conclude with `hm`. Set `S` to `Localization.AtPrime m`. Establish `hdvr : IsDiscreteValuationRing S` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hmbot S`. Establish `hreg : IsRegularLocalRing S` using `inferInstance`.

Establish `hsm : Algebra.FormallySmooth Ω S` using `GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField Ω S`. Establish `het : Algebra.FormallyEtale Ω (ResidueField S)` using `GlobalTheory.formallyEtale_residueField_of_isMaximal Ω Ω m S`. Take `⟨_, hrk⟩` from `GlobalTheory.free_and_finrank_kaehler_eq_finrank_cotangentSpace Ω S`. Establish `hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1`. Establish `h1` using `(IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hreg`.

Rewrite `h1` using `[IsDiscreteValuationRing.ringKrullDim_eq_one S]`. Conclude with `h1` after adjusting the coercions. Establish `hfp : Algebra.FinitePresentation Ω R` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `hsa : Algebra.IsSmoothAt Ω m` using `hsm`. Conclude with `GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt Ω m (hrk.trans hcot)`.
-/
private theorem exists_away (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    [Algebra Ω R] [Algebra.FiniteType Ω R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) (m : Ideal R) [hm : m.IsMaximal] :
    ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) := by
  have hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Ω R
  have hkd : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hdim
  have hdl : Ring.DimensionLEOne R :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have hded : IsDedekindDomain R := { }
  have hmbot : m ≠ ⊥ := by
    intro h
    apply hnf
    rw [Ring.isField_iff_maximal_bot]
    rw [← h]
    exact hm
  let S := Localization.AtPrime m
  have hdvr : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hmbot S
  have hreg : IsRegularLocalRing S := inferInstance
  have hsm : Algebra.FormallySmooth Ω S :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField Ω S
  have het : Algebra.FormallyEtale Ω (ResidueField S) :=
    GlobalTheory.formallyEtale_residueField_of_isMaximal Ω Ω m S
  obtain ⟨_, hrk⟩ := GlobalTheory.free_and_finrank_kaehler_eq_finrank_cotangentSpace Ω S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hreg
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one S] at h1
    exact_mod_cast h1
  have hfp : Algebra.FinitePresentation Ω R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsa : Algebra.IsSmoothAt Ω m := hsm
  exact GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt Ω m (hrk.trans hcot)

/- English proof (translation)
Use `letI : Algebra Ω R := ψ.toAlgebra`. Use `haveI : Algebra.FiniteType Ω R := hft`. Use `⟨{t | RingHom.IsStandardSmoothOfRelativeDimension 1 ((algebraMap R (Localization.Away t)).comp ψ)}, ?_, fun t ht => ht⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨f, hf, hsm⟩` from `exists_away Ω R hdim hnf M`. Apply `hf` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Apply `Ideal.subset_span` to reduce the goal to its premises. Establish `heq : ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra = (inferInstance : Algebra Ω (Localization.Away f))` using `Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply Ω R _ r).symm)`.

Use `show @Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) _ _ ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra`. Rewrite using `[heq]`. Conclude with `hsm`.
-/
private theorem locally_of_ringHom (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    (ψ : Ω →+* R) (hft : ψ.FiniteType) (hic : IsIntegrallyClosed R)
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ := by
  letI : Algebra Ω R := ψ.toAlgebra
  haveI : Algebra.FiniteType Ω R := hft
  refine ⟨{t | RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap R (Localization.Away t)).comp ψ)}, ?_, fun t ht => ht⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, hsm⟩ := exists_away Ω R hdim hnf M
  apply hf
  apply hle
  apply Ideal.subset_span
  have heq : ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra =
      (inferInstance : Algebra Ω (Localization.Away f)) :=
    Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply Ω R _ r).symm)
  show @Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) _ _
    ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra
  rw [heq]
  exact hsm

end UpperTheory.LocallyOfRingHomAway

/- English proof (translation)
Introduce `Ω _ _ C c hint hlft hic hdim`. Establish `key : ∀ (V : C.Opens) (hV : IsAffineOpen V) (a b : C), a ∈ V → b ∈ V → a ≠ b → RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (c.appLE ⊤ V (by simp)).hom`. Introduce `V hV a b ha hb hab`. Use `haveI : Nonempty V := ⟨⟨a, ha⟩⟩`. Establish `hdom : IsDomain Γ(C, V)` using `inferInstance`.

Set `ι` to `(Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv`. Set `ψ : Ω →+* Γ(C, V)` to `(c.appLE ⊤ V (by simp)).hom.comp ι.symm.toRingHom`. Establish `hφ : (c.appLE ⊤ V (by simp)).hom = ψ.comp ι.toRingHom`. Use extensionality with `r`. Simplify using `[ψ]`.

Rewrite using `[hφ]`. Apply `(RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right` to reduce the goal to its premises. Apply `UpperTheory.LocallyOfRingHomAway.locally_of_ringHom Ω Γ(C, V) ψ` to reduce the goal to its premises. Establish `hft : (c.appLE ⊤ V (by simp)).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType c hlft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _`. Conclude with `hft.comp (RingHom.FiniteType.of_surjective _ ι.symm.surjective)`.

Use `IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)` and prove the remaining obligations. Set `y : PrimeSpectrum Γ(C, V)` to `⟨p, hp.isPrime⟩`. Establish `hy : hV.fromSpec y ∈ V`. Establish `: hV.fromSpec y ∈ Set.range hV.fromSpec` using `⟨y, rfl⟩`. Rewrite `this` using `[hV.range_fromSpec]`. Then use the resulting hypothesis.

Use `letI := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨hV.fromSpec y, hy⟩`. Use `haveI hloc : IsLocalization p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) := hV.isLocalization_stalk' y hy`. Conclude with `(hic (hV.fromSpec y)).of_equiv (IsLocalization.algEquiv p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime p)).toRingEquiv`. Rewrite using `[← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)]`. Express the relevant statement in the definitionally equal form `topologicalKrullDim (Spec Γ(C, V)) ≤ 1`.

Rewrite using `[← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]`. Conclude with `(topologicalKrullDim_subspace_le C V).trans hdim.le`. Introduce `hf`. Use `letI := hf.toField`. Establish `ha' : a ∈ Set.range hV.fromSpec` using `by rw [hV.range_fromSpec]; exact ha`.

Establish `hb' : b ∈ Set.range hV.fromSpec` using `by rw [hV.range_fromSpec]; exact hb`. Take `⟨pa, rfl⟩` from `ha'`. Take `⟨pb, rfl⟩` from `hb'`. Establish `hss : Subsingleton (PrimeSpectrum Γ(C, V))` using `inferInstance`. Conclude with `hab (congrArg _ (hss.elim pa pb))`.

Establish `hgen : ∀ (W : C.Opens) (z : C), z ∈ W → genericPoint C ∈ W`. Introduce `W z hz`. Conclude with `((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hz⟩`. Establish `hexists : ∃ z : C, z ≠ genericPoint C`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Establish `hsub : Subsingleton (TopologicalSpace.IrreducibleCloseds C)`. Use `⟨fun s t => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `s.isIrreducible.nonempty`. Take `⟨q, hq⟩` from `t.isIrreducible.nonempty`.

Use extensionality with `y`. Rewrite using `[h y]`. Conclude with `⟨fun _ => h q ▸ hq, fun _ => h p ▸ hp⟩`. Establish `h0` using `Order.krullDim_nonpos_of_subsingleton (α := TopologicalSpace.IrreducibleCloseds C)`. Unfold `topologicalKrullDim at hdim`.

Rewrite `h0` using `[hdim]`. Conclude with `absurd h0 (by norm_num)`. Rewrite using `[HasRingHomProperty.iff_exists_appLE (P := @SmoothOfRelativeDimension 1) (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)]`. Introduce `x`. Distinguish the cases in `hx : x = genericPoint C`.

Take `⟨z, hz⟩` from `hexists`. Take `⟨W, hW, hzW, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)`. Use `⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hx ▸ hgen W z hzW, by simp, ?_⟩` and prove the remaining obligations. Conclude with `key W hW z (genericPoint C) hzW (hgen W z hzW) hz`. Take `⟨W, hW, hxW, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)`.

Use `⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hxW, by simp, ?_⟩` and prove the remaining obligations. Conclude with `key W hW x (genericPoint C) hxW (hgen W x hxW) hx`.
-/
theorem UpperTheory.smooth_of_normal_curve_perfectField :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hint hlft hic hdim
  have key : ∀ (V : C.Opens) (hV : IsAffineOpen V) (a b : C), a ∈ V → b ∈ V → a ≠ b →
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
        (c.appLE ⊤ V (by simp)).hom := by
    intro V hV a b ha hb hab
    haveI : Nonempty V := ⟨⟨a, ha⟩⟩
    have hdom : IsDomain Γ(C, V) := inferInstance
    let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
    let ψ : Ω →+* Γ(C, V) := (c.appLE ⊤ V (by simp)).hom.comp ι.symm.toRingHom
    have hφ : (c.appLE ⊤ V (by simp)).hom = ψ.comp ι.toRingHom := by
      ext r
      simp [ψ]
    rw [hφ]
    apply (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right
    apply UpperTheory.LocallyOfRingHomAway.locally_of_ringHom Ω Γ(C, V) ψ
    · have hft : (c.appLE ⊤ V (by simp)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType c hlft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact hft.comp (RingHom.FiniteType.of_surjective _ ι.symm.surjective)
    · refine IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)
      let y : PrimeSpectrum Γ(C, V) := ⟨p, hp.isPrime⟩
      have hy : hV.fromSpec y ∈ V := by
        have : hV.fromSpec y ∈ Set.range hV.fromSpec := ⟨y, rfl⟩
        rwa [hV.range_fromSpec] at this
      letI := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨hV.fromSpec y, hy⟩
      haveI hloc : IsLocalization p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) :=
        hV.isLocalization_stalk' y hy
      exact (hic (hV.fromSpec y)).of_equiv
        (IsLocalization.algEquiv p.primeCompl (C.presheaf.stalk (hV.fromSpec y))
          (Localization.AtPrime p)).toRingEquiv
    · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)]
      change topologicalKrullDim (Spec Γ(C, V)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le C V).trans hdim.le
    · intro hf
      letI := hf.toField
      have ha' : a ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact ha
      have hb' : b ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hb
      obtain ⟨pa, rfl⟩ := ha'
      obtain ⟨pb, rfl⟩ := hb'
      have hss : Subsingleton (PrimeSpectrum Γ(C, V)) := inferInstance
      exact hab (congrArg _ (hss.elim pa pb))
  have hgen : ∀ (W : C.Opens) (z : C), z ∈ W → genericPoint C ∈ W := by
    intro W z hz
    exact ((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hz⟩
  have hexists : ∃ z : C, z ≠ genericPoint C := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton (TopologicalSpace.IrreducibleCloseds C) := by
      refine ⟨fun s t => ?_⟩
      obtain ⟨p, hp⟩ := s.isIrreducible.nonempty
      obtain ⟨q, hq⟩ := t.isIrreducible.nonempty
      ext y
      rw [h y]
      exact ⟨fun _ => h q ▸ hq, fun _ => h p ▸ hp⟩
    have h0 := Order.krullDim_nonpos_of_subsingleton (α := TopologicalSpace.IrreducibleCloseds C)
    unfold topologicalKrullDim at hdim
    rw [hdim] at h0
    exact absurd h0 (by norm_num)
  rw [HasRingHomProperty.iff_exists_appLE (P := @SmoothOfRelativeDimension 1)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)]
  intro x
  by_cases hx : x = genericPoint C
  · obtain ⟨z, hz⟩ := hexists
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hx ▸ hgen W z hzW, by simp, ?_⟩
    exact key W hW z (genericPoint C) hzW (hgen W z hzW) hz
  · obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hxW, by simp, ?_⟩
    exact key W hW x (genericPoint C) hxW (hgen W x hxW) hx
