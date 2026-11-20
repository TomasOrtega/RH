import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y}`. Introduce `W hW hyW`. Establish `hWc : IsClosed W` using `isClosed_of_mem_irreducibleComponents W hW`. Establish `hgen` using `hW.1.isGenericPoint_genericPoint_closure`. Rewrite `hgen` using `[hWc.closure_eq]`.

Establish `hcl : closure {hW.1.genericPoint} = W` using `hgen`. Establish `hsub : W ⊆ closure {z | z ⤳ y}`. Rewrite using `[← hcl]`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))`. Conclude with `le_antisymm hsub (hW.2 hG.closure hsub)`.

Set `C` to `irreducibleComponent y`. Use `⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.sUnion_eq_biUnion, isOpen_compl_iff]`. Conclude with `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1`. Simplify using `only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_diff, Set.mem_singleton_iff, not_exists, not_and, and_imp]`.

Introduce `W hW hne hyW`. Conclude with `hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y) mem_irreducibleComponent).symm)`. Apply `isIrreducible_iff_closure.mp` to reduce the goal to its premises. Rewrite using `[closure_sUnion_irreducibleComponents_sdiff_singleton TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents y)]`. Conclude with `isIrreducible_irreducibleComponent`.
-/
private theorem exists_open_irreducible_nhds_of_generizations {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [TopologicalSpace.NoetherianSpace Y] (y : Y) (hG : IsIrreducible {z | z ⤳ y}) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsIrreducible U := by
  have key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y} := by
    intro W hW hyW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hgen := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hcl : closure {hW.1.genericPoint} = W := hgen
    have hsub : W ⊆ closure {z | z ⤳ y} := by
      rw [← hcl]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))
    exact le_antisymm hsub (hW.2 hG.closure hsub)
  let C := irreducibleComponent y
  refine ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_diff, Set.mem_singleton_iff,
      not_exists, not_and, and_imp]
    intro W hW hne hyW
    exact hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y)
      mem_irreducibleComponent).symm)
  · apply isIrreducible_iff_closure.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents y)]
    exact isIrreducible_irreducibleComponent

/- English proof (translation)
Use `IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_` and prove the remaining obligations. Set `y : PrimeSpectrum Γ(X, U)` to `⟨p, hp.isPrime⟩`. Establish `hy : hU.fromSpec y ∈ U` using `hU.range_fromSpec.le ⟨y, rfl⟩`. Use `letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩`. Use `haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) := hU.isLocalization_stalk' y hy`.

Express the relevant statement in the definitionally equal form `IsIntegrallyClosed (Localization.AtPrime y.asIdeal)`. Conclude with `(h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv`.
-/
private theorem isIntegrallyClosed_affine_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  change IsIntegrallyClosed (Localization.AtPrime y.asIdeal)
  exact (h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv

/- English proof (translation)
Introduce `S _ hN x`. Use `haveI : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1`. Take `⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `haveI : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact`. Use `haveI : IsNoetherian V.toScheme := {}`.

Establish `hns : TopologicalSpace.NoetherianSpace V.toScheme` using `inferInstance`. Establish `hqs : QuasiSober V.toScheme` using `inferInstance`. Establish `hG : IsIrreducible {z | z ⤳ x}`. Rewrite using `[← Scheme.range_fromSpecStalk]`. Use `haveI : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace`.

Rewrite using `[← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (S.fromSpecStalk x).continuous.continuousOn`. Establish `hGV : {z | z ⤳ x} ⊆ (V : Set S)` using `fun z hz => hz.mem_open V.isOpen hxV`. Establish `hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩}`. Establish `he : {z : V | z ⤳ ⟨x, hxV⟩} = Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V))`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩`. Introduce and unpack `⟨w, rfl⟩`.

Conclude with `(Topology.IsInducing.subtypeVal.specializes_iff).mp w.2`. Rewrite using `[he, ← Set.image_univ]`. Use `haveI : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (by fun_prop : Continuous _).continuousOn`. Take `⟨W, hWo, hxW, hWi⟩` from `@exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'`.

Establish `hW'o : IsOpen (Subtype.val '' W : Set S)` using `V.isOpen.isOpenMap_subtype_val W hWo`. Take `⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o`. Establish `hUi : IsIrreducible (U : Set S)` using `⟨⟨x, hxU⟩, (hWi.image _ continuous_subtype_val.continuousOn).2.open_subset U.isOpen hUW⟩`. Use `haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi`. Use `haveI : IsReduced S := isReduced_of_isReduced_stalk S`.

Use `haveI : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _`. Use `haveI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩`. Use `haveI : IsDomain Γ(S, U) := MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv`. Conclude with `⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nmlNoeth_of :
    NmlNoeth := by
  intro S _ hN x
  haveI : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1
  obtain ⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact
  haveI : IsNoetherian V.toScheme := {}
  have hns : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hqs : QuasiSober V.toScheme := inferInstance
  have hG : IsIrreducible {z | z ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (S.fromSpecStalk x).continuous.continuousOn
  have hGV : {z | z ⤳ x} ⊆ (V : Set S) := fun z hz => hz.mem_open V.isOpen hxV
  have hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩} := by
    have he : {z : V | z ⤳ ⟨x, hxV⟩} =
        Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩
      · rintro ⟨w, rfl⟩
        exact (Topology.IsInducing.subtypeVal.specializes_iff).mp w.2
    rw [he, ← Set.image_univ]
    haveI : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (by fun_prop : Continuous _).continuousOn
  obtain ⟨W, hWo, hxW, hWi⟩ := @exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'
  have hW'o : IsOpen (Subtype.val '' W : Set S) := V.isOpen.isOpenMap_subtype_val W hWo
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o
  have hUi : IsIrreducible (U : Set S) :=
    ⟨⟨x, hxU⟩, (hWi.image _ continuous_subtype_val.continuousOn).2.open_subset U.isOpen hUW⟩
  haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  haveI : IsDomain Γ(S, U) :=
    MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact ⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩
