import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.Model

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hηU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hV : IsAffineOpen (ν ⁻¹ᵁ U)` using `hU'.preimage ν`. Establish `hnV : n ∈ ν ⁻¹ᵁ U` using `show ν n ∈ U from hn ▸ hηU`. Use `haveI : Nonempty U := ⟨⟨_, hηU⟩⟩`.

Use `haveI : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨_, hnV⟩⟩`. Set `φ` to `ν.appLE U (ν ⁻¹ᵁ U) le_rfl`. Establish `hfin : φ.hom.Finite`. Use `Scheme.Hom.finite_app ν U hU'` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.app_eq_appLE]`. Then use the resulting hypothesis.

Use `letI := φ.hom.toAlgebra`. Use `haveI : Algebra.IsIntegral Γ(X, U) Γ(N, ν ⁻¹ᵁ U) := ⟨fun b => hfin.to_isIntegral b⟩`. Establish `hcomm` using `IsAffineOpen.SpecMap_appLE_fromSpec ν hU' hV le_rfl`. Use `set p := hV.primeIdealOf ⟨n, hnV⟩`. Establish `hp : hV.fromSpec p = n` using `hV.fromSpec_primeIdealOf ⟨n, hnV⟩`.

Establish `h1 : hU'.fromSpec (Spec.map φ p) = hU'.fromSpec ⟨⊥, inferInstance⟩`. Rewrite using `[map_bot_eq_genericPoint (A := Γ(X, U)) hU'.fromSpec, ← hn, ← hp]`. Conclude with `congr($hcomm p)`. Establish `h2` using `hU'.fromSpec.isOpenEmbedding.injective h1`. Establish `h3 : p.asIdeal.comap (algebraMap Γ(X, U) Γ(N, ν ⁻¹ᵁ U)) = ⊥` using `congrArg PrimeSpectrum.asIdeal h2`.

Establish `h4 : p = ⟨⊥, inferInstance⟩` using `PrimeSpectrum.ext (Ideal.eq_bot_of_comap_eq_bot h3)`. Rewrite using `[← hp, h4]`. Conclude with `map_bot_eq_genericPoint (A := Γ(N, ν ⁻¹ᵁ U)) hV.fromSpec`.
-/
theorem eq_genericPoint_of_isFinite {X N : Scheme.{0}} [IsIntegral X] [IsIntegral N] (ν : N ⟶ X)
    [IsFinite ν] {n : N} (hn : ν n = genericPoint X) : n = genericPoint N := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := hU'.preimage ν
  have hnV : n ∈ ν ⁻¹ᵁ U := show ν n ∈ U from hn ▸ hηU
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨_, hnV⟩⟩
  let φ := ν.appLE U (ν ⁻¹ᵁ U) le_rfl
  have hfin : φ.hom.Finite := by
    have := Scheme.Hom.finite_app ν U hU'
    rwa [Scheme.Hom.app_eq_appLE] at this
  letI := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(X, U) Γ(N, ν ⁻¹ᵁ U) :=
    ⟨fun b => hfin.to_isIntegral b⟩
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec ν hU' hV le_rfl
  set p := hV.primeIdealOf ⟨n, hnV⟩
  have hp : hV.fromSpec p = n := hV.fromSpec_primeIdealOf ⟨n, hnV⟩
  have h1 : hU'.fromSpec (Spec.map φ p) = hU'.fromSpec ⟨⊥, inferInstance⟩ := by
    rw [map_bot_eq_genericPoint (A := Γ(X, U)) hU'.fromSpec, ← hn, ← hp]
    exact congr($hcomm p)
  have h2 := hU'.fromSpec.isOpenEmbedding.injective h1
  have h3 : p.asIdeal.comap (algebraMap Γ(X, U) Γ(N, ν ⁻¹ᵁ U)) = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h2
  have h4 : p = ⟨⊥, inferInstance⟩ := PrimeSpectrum.ext (Ideal.eq_bot_of_comap_eq_bot h3)
  rw [← hp, h4]
  exact map_bot_eq_genericPoint (A := Γ(N, ν ⁻¹ᵁ U)) hV.fromSpec

/- English proof (translation)
Use `set η := genericPoint Z.X`. Set `u : Spec (.of (Z.X.residueField η)) ⟶ Z.X` to `Spec.map (Z.X.residue η) ≫ Z.X.fromSpecStalk η`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (u ≫ Z.str)`. Establish `hu : u (IsLocalRing.closedPoint (Z.X.residueField η)) = η` using `Scheme.fromSpecResidueField_apply η _`. Establish `hφinj : Function.Injective φ.hom`.

Establish `hη : (Z.str η).asIdeal = ⊥` using `mem_gen_iff_eq_bot.1 Z.genericPoint_mem_gen`. Establish `e : Spec.map φ (IsLocalRing.closedPoint (Z.X.residueField η)) = Z.str η`. Rewrite using `[hφ]`. Conclude with `congrArg Z.str hu`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`.

Establish `e'` using `congrArg PrimeSpectrum.asIdeal e`. Rewrite `e'` using `[hη]`. Rewrite using `[← e']`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `_ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal _`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]`. Both sides reduce to the same expression. Use `haveI : CharZero (Z.X.residueField η) := charZero_of_injective_ringHom hφinj`. Use `haveI : CharZero (IsLocalRing.ResidueField (Z.X.presheaf.stalk η)) := charZero_of_injective_ringHom hφinj`. Use `haveI : LocallyOfFiniteType Z.str := inferInstance`.

Establish `hfin : IsFinite u.fromNormalization` using `GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) Z.str η (Z.X.residue η) (RingHom.FiniteType.of_surjective _ (Z.X.residue_surjective η)).essFiniteType`. Set `ν` to `u.fromNormalization`. Use `haveI : Flat (u.fromNormalization ≫ Z.str) := by`. Establish `: Flat (u.toNormalization ≫ u.fromNormalization ≫ Z.str)`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]`.

Conclude with `Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)`. Conclude with `flat_normalization u _`. Set `Z' : Model O` to `{ X := u.normalization str := ν ≫ Z.str isIntegral := inferInstance isProjOver := isProjOver_comp_of_isFinite ν Z.isProjOver flat := ‹_› }`. Establish `hrange : Set.range ν = Set.univ`. Establish `hcl : IsClosed (Set.range ν)` using `ν.isClosedMap.isClosed_range`.

Establish `hmem : η ∈ Set.range ν` using `⟨u.toNormalization (IsLocalRing.closedPoint _), by`. Express the relevant statement in the definitionally equal form `(u.toNormalization ≫ u.fromNormalization) _ = η`. Rewrite using `[Scheme.Hom.toNormalization_fromNormalization]`. Conclude with `hu⟩`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations.

Rewrite using `[← (genericPoint_spec Z.X).def]`. Conclude with `hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)`. Use `haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩`. Set `n : Model.Hom Z' Z` to `⟨ν, rfl⟩`. Use `⟨Z', n, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_⟩` and prove the remaining obligations.

Establish `hdim` using `topologicalKrullDim_genFibre O Z Z' n`. Use `haveI : Subsingleton n.genFibre := by`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint Z'.X` using `fun c => by`.

Establish `hc : (ν.fiberι η) c ∈ ν ⁻¹' {η}`. Rewrite using `[← Scheme.Hom.range_fiberι]`. Conclude with `⟨c, rfl⟩`. Conclude with `eq_genericPoint_of_isFinite ν hc`. Conclude with `(ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)`.

Establish `h0` using `topologicalKrullDim_zero_of_discreteTopology n.genFibre`. Rewrite `h0` using `[hdim]`. Establish `h1 : n.relDim ≤ 0` using `by exact_mod_cast h0`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_normal_hom (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] (Z : Model O) :
    ∃ (Z' : Model O) (n : Model.Hom Z' Z), GlobalTheory.IsNormalScheme Z'.X ∧ n.relDim = 0 := by
  set η := genericPoint Z.X
  let u : Spec (.of (Z.X.residueField η)) ⟶ Z.X := Spec.map (Z.X.residue η) ≫ Z.X.fromSpecStalk η
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ Z.str)
  have hu : u (IsLocalRing.closedPoint (Z.X.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have hφinj : Function.Injective φ.hom := by
    have hη : (Z.str η).asIdeal = ⊥ := mem_gen_iff_eq_bot.1 Z.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint (Z.X.residueField η)) = Z.str η := by
      rw [hφ]
      exact congrArg Z.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero (Z.X.residueField η) := charZero_of_injective_ringHom hφinj
  haveI : CharZero (IsLocalRing.ResidueField (Z.X.presheaf.stalk η)) := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType Z.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) Z.str η (Z.X.residue η)
      (RingHom.FiniteType.of_surjective _ (Z.X.residue_surjective η)).essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ Z.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ Z.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let Z' : Model O :=
    { X := u.normalization
      str := ν ≫ Z.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν Z.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint _), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec Z.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom Z' Z := ⟨ν, rfl⟩
  refine ⟨Z', n, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_⟩
  have hdim := topologicalKrullDim_genFibre O Z Z' n
  haveI : Subsingleton n.genFibre := by
    constructor
    intro a b
    have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint Z'.X := fun c => by
      have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
      exact eq_genericPoint_of_isFinite ν hc
    exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
  have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
  rw [hdim] at h0
  have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
  omega

end GlobalTheory.Vert.Model

end
