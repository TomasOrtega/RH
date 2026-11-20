import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProperCover

/- English proof (translation)
Substitute `hx` using the available equality. Use `letI := (X.evaluation U _ hxU).hom.toAlgebra`. Use `haveI : Nonempty U := ⟨⟨_, hxU⟩⟩`. Use `functionField_isFractionRing_of_isAffineOpen X U hU` as an intermediate fact. Set `φ : X.functionField →+* X.residueField (genericPoint X)` to `(X.residue _).hom`.

Set `e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X)` to `{ RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with commutes' := fun _ => rfl }`. Conclude with `IsLocalization.isLocalization_of_algEquiv _ e`.
-/
theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

/- English proof (translation)
Introduce `a b h`. Apply `germ_injective_of_isIntegral X _ hV` to reduce the goal to its premises. Set `φ : X.functionField →+* X.residueField (genericPoint X)` to `(X.residue _).hom`. Apply `φ.injective` to reduce the goal to its premises. Conclude with `h`.
-/
theorem evaluation_genericPoint_injective (X : Scheme.{0}) [IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) : Function.Injective (X.evaluation V (genericPoint X) hV) := by
  intro a b h
  apply germ_injective_of_isIntegral X _ hV
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  apply φ.injective
  exact h

/- English proof (translation)
Establish `hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U → topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U)` using `fun {X} U hU => by`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]`. Conclude with `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))`. Use `topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_` and prove the remaining obligations. Take `⟨U, hU, hxU, -⟩` from `Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))`.

Take `⟨V, hV, hxV, hVU⟩` from `Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)`. Use `⟨V, V.isOpen, hxV, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))` and prove the remaining obligations. Rewrite using `[hd U hU, hd V hV]`. Establish `: Nonempty U` using `⟨⟨_, hxU⟩⟩`.

Establish `: Nonempty V` using `⟨⟨_, hxV⟩⟩`. Establish `: IsNoetherianRing Γ(Z, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Use `letI := (f.appLE U V hVU).hom.toAlgebra`. Establish `: Algebra.FiniteType Γ(Z, U) Γ(Z', V)` using `f.finiteType_appLE hU hV hVU`. Establish `hηV : genericPoint Z' ∈ V` using `((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩`.

Establish `hyU : f (genericPoint Z') ∈ U` using `hVU hηV`. Use `letI := (Z.evaluation U _ hyU).hom.toAlgebra`. Use `letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra`. Use `letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) := (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI := isFractionRing_evaluation Z hU hg hyU`. Establish `: Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z')))` using `IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))`. Establish `: Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z'))` using `Module.finite_of_finrank_pos hdeg`. Establish `: Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z'))` using `Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _`. Establish `hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV = Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')`.

Rewrite using `[Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]`. Use `congr 1`. Simplify using `[Scheme.evaluation]`. Set `ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z')` to `{ (Z'.evaluation V _ hηV).hom with commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }`. Establish `hψ : Function.Injective ψ` using `evaluation_genericPoint_injective Z' V hηV`.

Establish `hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V))`. Establish `h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z')))`. Rewrite using `[IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z'))]`. Conclude with `(f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)`. Introduce `a b h`.

Apply `h1` to reduce the goal to its premises. Rewrite using `[← ψ.commutes, ← ψ.commutes, h]`. Establish `: FaithfulSMul Γ(Z, U) Γ(Z', V)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `: Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V)` using `Algebra.IsAlgebraic.of_injective ψ hψ`. Conclude with `GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _`.
-/
theorem dim_le_of_residueDegree_pos {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian Z] (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : 0 < f.residueDegree (genericPoint Z')) :
    topologicalKrullDim Z' ≤ topologicalKrullDim Z := by
  have hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := fun {X} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Z', V) := f.finiteType_appLE hU hV hVU
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos hdeg
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := evaluation_genericPoint_injective Z' V hηV
  have hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V)) := by
    have h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z'))) := by
      rw [IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
        (Z'.residueField (genericPoint Z'))]
      exact (f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)
    intro a b h
    apply h1
    rw [← ψ.commutes, ← ψ.commutes, h]
  have : FaithfulSMul Γ(Z, U) Γ(Z', V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _

/- English proof (translation)
Introduce `Z' Z _ _ _ f _ hd hg hdeg`. Establish `: IsDominant f` using `⟨(dense_iff_closure_eq.2 (genericPoint_spec Z)).mono (Set.singleton_subset_iff.2 ⟨_, hg⟩)⟩`. Use `surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range` as an intermediate fact. Use `le_antisymm ((dim_le_of_residueDegree_pos f hg hdeg).trans hd.le) ?_` and prove the remaining obligations. Rewrite using `[← hd]`.

Conclude with `PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective`.
-/
theorem dim_eq_one : ∀ (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z)
    [IsProper f], topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z →
    0 < f.residueDegree (genericPoint Z') → topologicalKrullDim Z' = 1 := by
  intro Z' Z _ _ _ f _ hd hg hdeg
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Z)).mono
    (Set.singleton_subset_iff.2 ⟨_, hg⟩)⟩
  have := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  refine le_antisymm ((dim_le_of_residueDegree_pos f hg hdeg).trans hd.le) ?_
  rw [← hd]
  exact PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective

end GlobalTheory.ProperCover
