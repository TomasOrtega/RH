import Mathlib
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroBotOfEff
import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IrreducibleComponentsOfSupport
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalNormalForm
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.GBnd

open FunctorialResolution FunctorialResolution.EmbeddedResolution

def IsCompOf {X : Type*} [TopologicalSpace X] (E C : Set X) : Prop :=
  IsIrreducible C ∧ C ⊆ E ∧ ∀ T : Set X, IsIrreducible T → T ⊆ E → C ⊆ T → T ⊆ C

/- English proof (translation)
Take `⟨z, hz, hTz⟩` from `(isIrreducible_iff_sUnion_isClosed.mp hT) (S.image (fun s : Closeds X => (s : Set X))) (by`. Introduce `z hz`. Take `⟨s, -, rfl⟩` from `Finset.mem_image.mp hz`. Conclude with `s.2)`. Use the proof step `(by`.

Rewrite using `[Finset.coe_image, Set.sUnion_image]`. Simplify using `using h)`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp hz`. Conclude with `⟨s, hs, hTz⟩`.
-/
theorem irreducible_subset_of_finset {X : Type*} [TopologicalSpace X] {T : Set X} (hT : IsIrreducible T)
    (S : Finset (Closeds X)) (h : T ⊆ ⋃ s ∈ S, (s : Set X)) : ∃ s ∈ S, T ⊆ (s : Set X) := by
  classical
  obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hT) (S.image (fun s : Closeds X => (s : Set X)))
    (by
      intro z hz
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hz
      exact s.2)
    (by
      rw [Finset.coe_image, Set.sUnion_image]
      simpa using h)
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨s, hs, hTz⟩

/- English proof (translation)
Take `⟨S, hSirr, hSE⟩` from `TopologicalSpace.NoetherianSpace.exists_finset_irreducible E`. Establish `hE : (E : Set X) = ⋃ s ∈ S, (s : Set X)`. Rewrite using `[hSE, Closeds.coe_finset_sup]`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hirr : ∀ s ∈ S, IsIrreducible (s : Set X)` using `fun s hs => hSirr ⟨s, hs⟩`. Establish `hsub : ∀ s ∈ S, (s : Set X) ⊆ E`. Introduce `s hs x hx`. Rewrite using `[hE]`. Conclude with `Set.mem_biUnion hs hx`.

Use `⟨S.filter (fun s => ∀ s' ∈ S, s ≤ s' → s' ≤ s), ?_, ?_⟩` and prove the remaining obligations. Introduce `C`. Rewrite using `[Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hC, hmax⟩`.

Use `⟨hirr C hC, hsub C hC, ?_⟩` and prove the remaining obligations. Introduce `T hT hTE hCT`. Take `⟨s', hs', hTs'⟩` from `irreducible_subset_of_finset hT S (hE ▸ hTE)`. Establish `h1 : C ≤ s'` using `fun x hx => hTs' (hCT hx)`. Conclude with `fun x hx => hmax s' hs' h1 (hTs' hx)`.

Introduce and unpack `⟨hCirr, hCE, hCmax⟩`. Take `⟨s, hs, hCs⟩` from `irreducible_subset_of_finset hCirr S (hE ▸ hCE)`. Establish `hsC : (s : Set X) ⊆ C` using `hCmax s (hirr s hs) (hsub s hs) hCs`. Establish `hCeq : C = s` using `SetLike.coe_injective (Set.Subset.antisymm hCs hsC)`. Substitute `hCeq` using the available equality.

Use `⟨hs, ?_⟩` and prove the remaining obligations. Introduce `s' hs' hle`. Conclude with `hCmax s' (hirr s' hs') (hsub s' hs') hle`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`.

Simplify using `only [Set.mem_iUnion, Finset.mem_filter] at hx`. Take `⟨C, ⟨hC, -⟩, hxC⟩` from `hx`. Conclude with `hsub C hC hxC`. Introduce `x hx`. Rewrite `hx` using `[hE]`.

Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨s, hs, hxs⟩` from `hx`. Take `⟨b, hsb, hbmax⟩` from `Finset.exists_le_maximal S hs`. Simplify using `only [Set.mem_iUnion, Finset.mem_filter]`. Conclude with `⟨b, ⟨hbmax.1, fun s' hs' h => hbmax.2 hs' h⟩, hsb hxs⟩`.
-/
theorem exists_finset_comps {X : Scheme.{0}} [IsNoetherian X] (E : Closeds X) :
    ∃ 𝒞 : Finset (Closeds X), (∀ C : Closeds X, C ∈ 𝒞 ↔ IsCompOf (E : Set X) (C : Set X)) ∧
      (⋃ C ∈ 𝒞, (C : Set X)) = E := by
  classical
  obtain ⟨S, hSirr, hSE⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible E
  have hE : (E : Set X) = ⋃ s ∈ S, (s : Set X) := by
    rw [hSE, Closeds.coe_finset_sup]
    ext x
    simp
  have hirr : ∀ s ∈ S, IsIrreducible (s : Set X) := fun s hs => hSirr ⟨s, hs⟩
  have hsub : ∀ s ∈ S, (s : Set X) ⊆ E := by
    intro s hs x hx
    rw [hE]
    exact Set.mem_biUnion hs hx
  refine ⟨S.filter (fun s => ∀ s' ∈ S, s ≤ s' → s' ≤ s), ?_, ?_⟩
  · intro C
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hC, hmax⟩
      refine ⟨hirr C hC, hsub C hC, ?_⟩
      intro T hT hTE hCT
      obtain ⟨s', hs', hTs'⟩ := irreducible_subset_of_finset hT S (hE ▸ hTE)
      have h1 : C ≤ s' := fun x hx => hTs' (hCT hx)
      exact fun x hx => hmax s' hs' h1 (hTs' hx)
    · rintro ⟨hCirr, hCE, hCmax⟩
      obtain ⟨s, hs, hCs⟩ := irreducible_subset_of_finset hCirr S (hE ▸ hCE)
      have hsC : (s : Set X) ⊆ C := hCmax s (hirr s hs) (hsub s hs) hCs
      have hCeq : C = s := SetLike.coe_injective (Set.Subset.antisymm hCs hsC)
      subst hCeq
      refine ⟨hs, ?_⟩
      intro s' hs' hle
      exact hCmax s' (hirr s' hs') (hsub s' hs') hle
  · apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion, Finset.mem_filter] at hx
      obtain ⟨C, ⟨hC, -⟩, hxC⟩ := hx
      exact hsub C hC hxC
    · intro x hx
      rw [hE] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      obtain ⟨b, hsb, hbmax⟩ := Finset.exists_le_maximal S hs
      simp only [Set.mem_iUnion, Finset.mem_filter]
      exact ⟨b, ⟨hbmax.1, fun s' hs' h => hbmax.2 hs' h⟩, hsb hxs⟩

open scoped TensorProduct

/- English proof (translation)
Establish `key : ∀ (b : A), b ∈ Ideal.span (Set.range y) → ∀ (hb : b ∈ IsLocalRing.maximalIdeal A), (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨y i, hy i⟩ : Fin d → IsLocalRing. …`. Introduce `b hb0`. Establish `hb' : b ∈ Submodule.span A (Set.range y)` using `hb0`. Use `clear hb0`. Proceed by induction on `hb' using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨i, rfl⟩` from `hz`. Introduce `hz'`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero`.

Introduce `hz'`. Establish `h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0` using `rfl`. Rewrite using `[h0, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add z z' hz hz' ihz ihz'`.

Introduce `hbb`. Establish `hzm : z ∈ IsLocalRing.maximalIdeal A` using `by rw [← hspan]; exact hz`. Establish `hzm' : z' ∈ IsLocalRing.maximalIdeal A` using `by rw [← hspan]; exact hz'`. Establish `hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩` using `rfl`. Rewrite using `[hsum, map_add]`.

Conclude with `Submodule.add_mem _ (ihz hzm) (ihz' hzm')`. Consider the case `smul c z hz ih`. Introduce `hbb`. Establish `hzm : z ∈ IsLocalRing.maximalIdeal A` using `by rw [← hspan]; exact hz`. Establish `hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩` using `rfl`.

Rewrite using `[hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]`. Conclude with `Submodule.smul_mem _ _ (ih hzm)`. Establish `hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨y i, hy i⟩ : Fin d → IsLocalRing.CotangentSpace A))`. Introduce `v _`. Take `⟨⟨b, hb⟩, rfl⟩` from `Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v`.

Conclude with `key b (by rw [hspan]; exact hb) hb`. Establish `hcard0 : ((d : ℕ) : WithBot ℕ∞) = ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) : WithBot ℕ∞)` using `hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm`. Establish `hcard : Fintype.card (Fin d) = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)`. Rewrite using `[Fintype.card_fin]`. Conclude with `hcard0` after adjusting the coercions.

Conclude with `linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard`.
-/
theorem linearIndependent_toCotangent_of_span {A : Type*} [CommRing A] [IsLocalRing A] [IsRegularLocalRing A]
    (d : ℕ) (y : Fin d → A) (hy : ∀ i, y i ∈ IsLocalRing.maximalIdeal A)
    (hspan : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A)
    (hdim : (d : WithBot ℕ∞) = ringKrullDim A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨y i, hy i⟩ :
        Fin d → IsLocalRing.CotangentSpace A) := by
  classical
  have key : ∀ (b : A), b ∈ Ideal.span (Set.range y) →
      ∀ (hb : b ∈ IsLocalRing.maximalIdeal A),
        (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈
          Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨y i, hy i⟩ :
              Fin d → IsLocalRing.CotangentSpace A)) := by
    intro b hb0
    have hb' : b ∈ Submodule.span A (Set.range y) := hb0
    clear hb0
    induction hb' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
        intro hz'
        have h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hzm' : z' ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz'
        have hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add]
        exact Submodule.add_mem _ (ihz hzm) (ihz' hzm')
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]
        exact Submodule.smul_mem _ _ (ih hzm)
  have hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨y i, hy i⟩ :
        Fin d → IsLocalRing.CotangentSpace A)) := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard0 : ((d : ℕ) : WithBot ℕ∞) =
      ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) :
        WithBot ℕ∞) :=
    hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm
  have hcard : Fintype.card (Fin d) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast hcard0
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard

/- English proof (translation)
Set `φ : IsLocalRing.ResidueField A ⊗[A] IsLocalRing.maximalIdeal A →ₗ[IsLocalRing.ResidueField A] IsLocalRing.CotangentSpace A` to `LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A).toCotangent`. Use `LinearIndependent.of_comp φ ?_` and prove the remaining obligations. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[φ, LinearMap.liftBaseChange_tmul]`.
-/
theorem linearIndependent_one_tmul_of_toCotangent {A : Type*} [CommRing A] [IsLocalRing A] {ι : Type*}
    (y : ι → IsLocalRing.maximalIdeal A)
    (h : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => (IsLocalRing.maximalIdeal A).toCotangent (y i) : ι → IsLocalRing.CotangentSpace A)) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i)) := by
  let φ : IsLocalRing.ResidueField A ⊗[A] IsLocalRing.maximalIdeal A →ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.CotangentSpace A :=
    LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (IsLocalRing.maximalIdeal A).toCotangent
  refine LinearIndependent.of_comp φ ?_
  convert h using 1
  funext i
  simp [φ, LinearMap.liftBaseChange_tmul]

/- English proof (translation)
Take `⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M), ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i` from `⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩`. Establish `hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)`. Introduce `c m`. Establish `hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m` using `(TensorProduct.smul_tmul c 1 m).symm`. Establish `hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c`.

Rewrite using `[Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]`. Establish `hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m` using `rfl`. Rewrite using `[hA1, hA2, hA3, mul_one]`. Establish `hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j)`. Introduce `i j`.

Establish `hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l`. Rewrite using `[hB' j]`. Use `conv_lhs => rw [← bA.sum_repr (G j)]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hkey, hbk l]`. Rewrite using `[hGj, Module.Basis.toMatrix_apply]`. Simplify using `only [Module.Basis.repr_sum_self]`. Establish `hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G)`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Module.Basis.toMatrix_apply]`. Conclude with `hmat i j`. Rewrite using `[← hdet]`.

Conclude with `(bk.isUnit_det B').ne_zero`.
-/
private theorem residue_det_ne_zero_of_basis_tmul' {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bA : Module.Basis ι A M) (G : ι → M)
    (B' : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M))
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    IsLocalRing.residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr (G j)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, Module.Basis.toMatrix_apply]
    simp only [Module.Basis.repr_sum_self]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero

/- English proof (translation)
Establish `instFEloc : Algebra.FormallyEtale S A` using `Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)`. Set `instPA : Algebra (MvPolynomial ι k) A` to `((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra`. Establish `instT1 : IsScalarTower (MvPolynomial ι k) S A` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply k S A x, IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]`.

Both sides reduce to the same expression. Establish `instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A` using `Algebra.FormallyEtale.comp (MvPolynomial ι k) S A`. Take `⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A), ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (EtaleCoordinates.basisKaehler k ι A i)` from `⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (EtaleCoordinates.basisKaehler k ι A), fun i => by simp⟩`. Take `⟨Jst, B, hbasisInl, hbasisInr⟩` from `EtaleCoordinates.exists_basis_sum_of_linearIndependent bk h (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (s i))) hsind`. Establish `hcard1 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card (Fin h ⊕ {j : ι // j ∈ Jst})` using `Module.finrank_eq_card_basis B`.

Establish `hcard2 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι` using `Module.finrank_eq_card_basis bk`. Establish `hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card ι`. Rewrite using `[← Fintype.card_sum]`. Conclude with `Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))`. Rewrite `hcard1` using `[Fintype.card_sum, Fintype.card_fin]`.

Establish `hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = h` using `by omega`. Establish `e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin h` using `Fintype.equivFinOfCardEq hcard4`. Take `⟨τ, hτl, hτr⟩ : ∃ τ : Fin h ⊕ {j : ι // j ∈ Jst} ≃ ι, (∀ l : Fin h, τ (Sum.inl l) = ((e.symm l : ι))) ∧ (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι))` from `⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))), fun l => rfl, fun j => rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = EtaleCoordinates.coord k ι S j) ∧ (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by`. Use `⟨fun j => if hj : j ∈ Jst then EtaleCoordinates.coord k ι S j else s (e ⟨j, hj⟩), fun j hj => ?_, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `dif_pos hj`. Conclude with `dif_neg x.2`. Establish `hbasisApply : ∀ x : Fin h ⊕ {j : ι // j ∈ Jst}, B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (w (τ x)))`. Introduce and unpack `(l | j)`. Rewrite using `[hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]`.

Rewrite using `[hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), EtaleCoordinates.basisKaehler_apply, EtaleCoordinates.algebraMap_coord]`. Establish `hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (w i))`. Introduce `i`. Rewrite using `[Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]`. Establish `hdetne` using `residue_det_ne_zero_of_basis_tmul' (EtaleCoordinates.basisKaehler k ι A) (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G`.

Establish `hdetA : algebraMap S A ((EtaleCoordinates.basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i))) = (EtaleCoordinates.basisKaehler k ι A).det (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i)))` using `EtaleCoordinates.algebraMap_det_basisKaehler k ι S A w`. Establish `hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A` using `IsLocalization.AtPrime.map_eq_maximalIdeal q A`. Use `⟨w, fun i => (e.symm i : ι), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hwn (e.symm i), Equiv.apply_symm_apply]`. Introduce `hgq`.

Apply `hdetne` to reduce the goal to its premises. Rewrite using `[← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]`. Conclude with `Ideal.mem_map_of_mem _ hgq`.
-/
theorem exists_coords_containing (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A]
    (h : ℕ) (s : Fin h → S)
    (hsind : LinearIndependent (IsLocalRing.ResidueField A)
      fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) :
    ∃ (w : ι → S) (t : Fin h → ι),
      (∀ i, w (t i) = s i) ∧
      (EtaleCoordinates.basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i)) ∉ q := by
  classical
  have instFEloc : Algebra.FormallyEtale S A :=
    Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)
  let instPA : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S A x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (EtaleCoordinates.basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (EtaleCoordinates.basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := EtaleCoordinates.exists_basis_sum_of_linearIndependent bk h
    (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hsind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin h ⊕ {j : ι // j ∈ Jst}) := Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = h := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin h := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin h ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin h, τ (Sum.inl l) = ((e.symm l : ι))) ∧
      (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι)) :=
    ⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = EtaleCoordinates.coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by
    refine ⟨fun j => if hj : j ∈ Jst then EtaleCoordinates.coord k ι S j else s (e ⟨j, hj⟩),
      fun j hj => ?_, fun x => ?_⟩
    · exact dif_pos hj
    · exact dif_neg x.2
  have hbasisApply : ∀ x : Fin h ⊕ {j : ι // j ∈ Jst},
      B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (w (τ x))) := by
    rintro (l | j)
    · rw [hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]
    · rw [hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), EtaleCoordinates.basisKaehler_apply,
        EtaleCoordinates.algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (w i)) := by
    intro i
    rw [Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_basis_tmul' (EtaleCoordinates.basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((EtaleCoordinates.basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (EtaleCoordinates.basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    EtaleCoordinates.algebraMap_det_basisKaehler k ι S A w
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  refine ⟨w, fun i => (e.symm i : ι), fun i => ?_, ?_⟩
  · rw [hwn (e.symm i), Equiv.apply_symm_apply]
  · intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq

/- English proof (translation)
Set `instKT : Algebra k T` to `((algebraMap S T).comp (algebraMap k S)).toAlgebra`. Set `instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T` to `((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra`. Establish `instTkS : IsScalarTower k S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `instTPS : IsScalarTower (MvPolynomial ι k) S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `instTkP : IsScalarTower k (MvPolynomial ι k) T` using `IsScalarTower.of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply k S T x, IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]`. Both sides reduce to the same expression. Establish `instFEST : Algebra.FormallyEtale S T` using `Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)`. Establish `instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T` using `Algebra.FormallyEtale.comp (MvPolynomial ι k) S T`. Establish `instFSkT : Algebra.FormallySmooth k T` using `Algebra.FormallySmooth.comp k (MvPolynomial ι k) T`.

Establish `hdet' : IsUnit ((EtaleCoordinates.basisKaehler k ι T).det fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i)))`. Rewrite using `[← EtaleCoordinates.algebraMap_det_basisKaehler k ι S T w]`. Conclude with `hdet`. Establish `h` using `EtaleCoordinates.formallyEtale_aeval_of_isUnit_det (EtaleCoordinates.basisKaehler k ι T) (fun i : ι => algebraMap S T (w i)) hdet'`. Conclude with `h`.
-/
private theorem formallyEtale_away_of_isUnit_det' (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (g : S) (T : Type*) [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers g) T]
    (w : ι → S)
    (hdet : IsUnit (algebraMap S T
      ((EtaleCoordinates.basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :
    @Algebra.FormallyEtale (MvPolynomial ι k) T _ _
      (RingHom.toAlgebra
        (MvPolynomial.eval₂Hom ((algebraMap S T).comp (algebraMap k S))
          (fun j : ι => algebraMap S T (w j)))) := by
  classical
  let instKT : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
  let instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T :=
    ((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instTkS : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTPS : IsScalarTower (MvPolynomial ι k) S T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTkP : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S T x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEST : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)
  have instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S T
  have instFSkT : Algebra.FormallySmooth k T :=
    Algebra.FormallySmooth.comp k (MvPolynomial ι k) T
  have hdet' : IsUnit ((EtaleCoordinates.basisKaehler k ι T).det
      fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i))) := by
    rw [← EtaleCoordinates.algebraMap_det_basisKaehler k ι S T w]
    exact hdet
  have h := EtaleCoordinates.formallyEtale_aeval_of_isUnit_det (EtaleCoordinates.basisKaehler k ι T)
    (fun i : ι => algebraMap S T (w i)) hdet'
  exact h

/- English proof (translation)
Take `⟨U₀, m, hxU₀, hU₀U, hU₀, ⟨c⟩⟩` from `exists_etaleChart_le p x U.1 hx`. Set `_ : Algebra k Γ(X, U₀)` to `sectionsAlgebra k p U₀`. Establish `hk : (algebraMap k Γ(X, U₀)) = sectionsAlgebraMap k p U₀` using `algebraMap_sectionsAlgebra k p U₀`. Set `_ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀)` to `c.algebra`. Establish `: IsScalarTower k (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀)` using `c.isScalarTower`.

Establish `: Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀)` using `c.algebra_formallyEtale hU₀`. Establish `: DecidableEq (ULift.{0} (Fin m))` using `Classical.decEq _`. Set `P : PrimeSpectrum Γ(X, U₀)` to `hU₀.primeIdealOf ⟨x, hxU₀⟩`. Set `_instStalk : Algebra k (X.presheaf.stalk x)` to `stalkAlgebra k p x`. Set `_instGerm : Algebra Γ(X, U₀) (X.presheaf.stalk x)` to `(X.presheaf.germ U₀ x hxU₀).hom.toAlgebra`.

Establish `: IsScalarTower k Γ(X, U₀) (X.presheaf.stalk x)` using `isScalarTower_stalk k p U₀ x hxU₀ (algebraMap_sectionsAlgebra k p U₀) (algebraMap_stalkAlgebra k p x) rfl`. Establish `: IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal` using `hU₀.isLocalization_stalk ⟨x, hxU₀⟩`. Establish `: Algebra.FormallySmooth k (X.presheaf.stalk x)` using `formallySmooth_stalk k p x`. Set `_instResidue : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))` to `((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra`. Establish `: IsScalarTower k (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `: Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))` using `formallySmooth_residueField k p x rfl`. Establish `: IsRegularLocalRing (X.presheaf.stalk x)` using `isRegularLocalRing_stalk_of_smooth p x`. Set `s : Fin n → Γ(X, U₀)` to `fun i => (X.presheaf.map (homOfLE hU₀U).op).hom (f i)`. Establish `hgerm : ∀ i, algebraMap Γ(X, U₀) (X.presheaf.stalk x) (s i) = X.presheaf.germ U.1 x hx (f i)`. Introduce `i`.

Conclude with `X.presheaf.germ_res_apply (homOfLE hU₀U) x hxU₀ (f i)`. Establish `hy : ∀ i, X.presheaf.germ U.1 x hx (f i) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)`. Introduce `i`. Rewrite using `[← hf.1]`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`.

Establish `hcot` using `linearIndependent_toCotangent_of_span n (fun i => X.presheaf.germ U.1 x hx (f i)) hy hf.1 hf.2`. Establish `htm` using `linearIndependent_one_tmul_of_toCotangent (fun i => (⟨X.presheaf.germ U.1 x hx (f i), hy i⟩ : IsLocalRing.maximalIdeal (X.presheaf.stalk x))) hcot`. Establish `hD` using `linearIndependent_tensor_D_of_maximalIdeal k (X.presheaf.stalk x) (fun i => (⟨X.presheaf.germ U.1 x hx (f i), hy i⟩ : IsLocalRing.maximalIdeal (X.presheaf.stalk x))) htm`. Establish `hsind : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x)) fun i : Fin n => (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x] KaehlerDifferential.D k (X.presheaf.stalk x) (algebraMap Γ(X, U₀) (X.presheaf.stalk x) (s i))`. Use `hD using 2 with i` and compare the differences between its conclusion and the goal.

Rewrite using `[hgerm i]`. Take `⟨w, t, hwt, hdetq⟩` from `exists_coords_containing k (ULift.{0} (Fin m)) Γ(X, U₀) P.asIdeal (X.presheaf.stalk x) n s hsind`. Use `set g := (EtaleCoordinates.basisKaehler k (ULift.{0} (Fin m)) Γ(X, U₀)).det (fun i => KaehlerDifferential.D k Γ(X, U₀) (w i)) with hg`. Establish `hfe` using `formallyEtale_away_of_isUnit_det' k (ULift.{0} (Fin m)) Γ(X, U₀) g (Localization.Away g) w (IsLocalization.map_units (Localization.Away g) ⟨g, Submonoid.mem_powers g⟩)`. Establish `hgq : g ∉ P.asIdeal` using `hdetq`.

Establish `hxU : x ∈ X.basicOpen g` using `mem_basicOpen_of_notMem_primeIdealOf hU₀ hxU₀ g hgq`. Set `_ : Algebra k Γ(X, X.basicOpen g)` to `sectionsAlgebra k p (X.basicOpen g)`. Set `_ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) (Localization.Away g)` to `RingHom.toAlgebra (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))`. Establish `: Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) (Localization.Away g)` using `hfe`. Set `_ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)` to `RingHom.toAlgebra (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))`.

Establish `: IsLocalization.Away g Γ(X, X.basicOpen g)` using `hU₀.isLocalization_basicOpen g`. Set `e : Localization.Away g ≃ₐ[Γ(X, U₀)] Γ(X, X.basicOpen g)` to `IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)`. Establish `hcomm : (e.toAlgHom.toRingHom).comp (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j))) = MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)) …`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Conclude with `e.commutes _`. Introduce `i`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Conclude with `e.commutes _`.

Set `E : Localization.Away g ≃ₐ[MvPolynomial (ULift.{0} (Fin m)) k] Γ(X, X.basicOpen g)` to `AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun z => congrArg (fun φ : MvPolynomial (ULift.{0} (Fin m)) k →+* Γ(X, X.basicOpen g) => φ z) hcomm)`. Establish `: Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)` using `Algebra.FormallyEtale.of_equiv E`. Establish `: Algebra.FiniteType k Γ(X, X.basicOpen g)` using `finiteType_sections k p ⟨X.basicOpen g, hU₀.basicOpen g⟩ (algebraMap_sectionsAlgebra k p (X.basicOpen g))`. Establish `: IsScalarTower k (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)`. Use `IsScalarTower.of_algebraMap_eq (fun a => ?_)` and prove the remaining obligations.

Establish `h1 : algebraMap (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) (algebraMap k (MvPolynomial (ULift.{0} (Fin m)) k) a) = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (algebraMap k Γ(X, U₀) a)`. Rewrite using `[MvPolynomial.algebraMap_eq]`. Conclude with `MvPolynomial.eval₂Hom_C _ _ a`. Rewrite using `[h1]`. Conclude with `(sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a).symm`.

Establish `: Algebra.FiniteType (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)` using `Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)`. Establish `: Algebra.FinitePresentation (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `: Algebra.Etale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)`. Apply the tactic sequence `constructor <;> infer_instance`. Establish `hC : ∀ a : k, (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))) (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a`.

Introduce `a`. Rewrite using `[MvPolynomial.eval₂Hom_C]`. Conclude with `sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a`. Establish `hX : ∀ i : ULift.{0} (Fin m), (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))) (MvPolynomial.X i) = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i)` using `fun i => MvPolynomial.eval₂Hom_X' _ _ i`. Establish `hfet : (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))).Etale` using `‹Algebra.Etale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)›`.

Take `⟨c', hc'⟩` from `exists_etaleChart_coord_eq p (hU₀.basicOpen g) (fun i : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i)) (MvPolynomial.eval₂Hom ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀))) (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.bas …`. Use `⟨X.basicOpen g, hU₀.basicOpen g, (X.basicOpen_le g).trans hU₀U, hxU, m, c', fun i => (t i).down, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hc' (t i).down]`. Use `show algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w (t i)) = _`. Rewrite using `[hwt i]`.

Use `show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((X.presheaf.map (homOfLE hU₀U).op).hom (f i)) = _`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_chart_coords_of_rsp {X : Scheme.{0}} {k : Type} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (n : ℕ)
    (f : Fin n → Γ(X, U.1)) (hf : FinalTheorems.Rsp (X.presheaf.stalk x) n (fun i => X.presheaf.germ U.1 x hx (f i))) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ U.1) (_ : x ∈ V) (m : ℕ) (c : EtaleChart p V m)
      (t : Fin n → Fin m), ∀ i, c.coord (t i) = (X.presheaf.map (homOfLE hVU).op).hom (f i) := by
  classical
  obtain ⟨U₀, m, hxU₀, hU₀U, hU₀, ⟨c⟩⟩ := exists_etaleChart_le p x U.1 hx
  let _ : Algebra k Γ(X, U₀) := sectionsAlgebra k p U₀
  have hk : (algebraMap k Γ(X, U₀)) = sectionsAlgebraMap k p U₀ :=
    algebraMap_sectionsAlgebra k p U₀
  let _ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀) := c.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀) := c.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, U₀) :=
    c.algebra_formallyEtale hU₀
  have : DecidableEq (ULift.{0} (Fin m)) := Classical.decEq _
  let P : PrimeSpectrum Γ(X, U₀) := hU₀.primeIdealOf ⟨x, hxU₀⟩
  let _instStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  let _instGerm : Algebra Γ(X, U₀) (X.presheaf.stalk x) :=
    (X.presheaf.germ U₀ x hxU₀).hom.toAlgebra
  have : IsScalarTower k Γ(X, U₀) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U₀ x hxU₀ (algebraMap_sectionsAlgebra k p U₀)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal := hU₀.isLocalization_stalk ⟨x, hxU₀⟩
  have : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  let _instResidue : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    formallySmooth_residueField k p x rfl
  have : IsRegularLocalRing (X.presheaf.stalk x) := isRegularLocalRing_stalk_of_smooth p x
  let s : Fin n → Γ(X, U₀) := fun i => (X.presheaf.map (homOfLE hU₀U).op).hom (f i)
  have hgerm : ∀ i, algebraMap Γ(X, U₀) (X.presheaf.stalk x) (s i) = X.presheaf.germ U.1 x hx (f i) := by
    intro i
    exact X.presheaf.germ_res_apply (homOfLE hU₀U) x hxU₀ (f i)
  have hy : ∀ i, X.presheaf.germ U.1 x hx (f i) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro i
    rw [← hf.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hcot := linearIndependent_toCotangent_of_span n (fun i => X.presheaf.germ U.1 x hx (f i)) hy hf.1 hf.2
  have htm := linearIndependent_one_tmul_of_toCotangent
    (fun i => (⟨X.presheaf.germ U.1 x hx (f i), hy i⟩ : IsLocalRing.maximalIdeal (X.presheaf.stalk x))) hcot
  have hD := linearIndependent_tensor_D_of_maximalIdeal k (X.presheaf.stalk x)
    (fun i => (⟨X.presheaf.germ U.1 x hx (f i), hy i⟩ : IsLocalRing.maximalIdeal (X.presheaf.stalk x))) htm
  have hsind : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x))
      fun i : Fin n => (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
        KaehlerDifferential.D k (X.presheaf.stalk x) (algebraMap Γ(X, U₀) (X.presheaf.stalk x) (s i)) := by
    convert hD using 2 with i
    rw [hgerm i]
  obtain ⟨w, t, hwt, hdetq⟩ := exists_coords_containing k (ULift.{0} (Fin m)) Γ(X, U₀) P.asIdeal
    (X.presheaf.stalk x) n s hsind
  set g := (EtaleCoordinates.basisKaehler k (ULift.{0} (Fin m)) Γ(X, U₀)).det
    (fun i => KaehlerDifferential.D k Γ(X, U₀) (w i)) with hg
  have hfe := formallyEtale_away_of_isUnit_det' k (ULift.{0} (Fin m)) Γ(X, U₀) g (Localization.Away g) w
    (IsLocalization.map_units (Localization.Away g) ⟨g, Submonoid.mem_powers g⟩)
  have hgq : g ∉ P.asIdeal := hdetq
  have hxU : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hU₀ hxU₀ g hgq
  let _ : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  let _ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) (Localization.Away g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) (Localization.Away g) := hfe
  let _ : Algebra (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU₀.isLocalization_basicOpen g
  let e : Localization.Away g ≃ₐ[Γ(X, U₀)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hcomm : (e.toAlgHom.toRingHom).comp
      (MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
      = MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact e.commutes _
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact e.commutes _
  let E : Localization.Away g ≃ₐ[MvPolynomial (ULift.{0} (Fin m)) k] Γ(X, X.basicOpen g) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
      (fun z => congrArg
        (fun φ : MvPolynomial (ULift.{0} (Fin m)) k →+* Γ(X, X.basicOpen g) => φ z) hcomm)
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FormallyEtale.of_equiv E
  have : Algebra.FiniteType k Γ(X, X.basicOpen g) :=
    finiteType_sections k p ⟨X.basicOpen g, hU₀.basicOpen g⟩
      (algebraMap_sectionsAlgebra k p (X.basicOpen g))
  have : IsScalarTower k (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    have h1 : algebraMap (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)
        (algebraMap k (MvPolynomial (ULift.{0} (Fin m)) k) a)
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (algebraMap k Γ(X, U₀) a) := by
      rw [MvPolynomial.algebraMap_eq]
      exact MvPolynomial.eval₂Hom_C _ _ a
    rw [h1]
    exact (sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a).symm
  have : Algebra.FiniteType (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{0} (Fin m)) k)
      Γ(X, X.basicOpen g) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g) := by
    constructor <;> infer_instance
  have hC : ∀ a : k, (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a := by
    intro a
    rw [MvPolynomial.eval₂Hom_C]
    exact sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a
  have hX : ∀ i : ULift.{0} (Fin m), (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.X i) = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i) :=
    fun i => MvPolynomial.eval₂Hom_X' _ _ i
  have hfet : (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) =>
        algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))).Etale :=
    ‹Algebra.Etale (MvPolynomial (ULift.{0} (Fin m)) k) Γ(X, X.basicOpen g)›
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p (hU₀.basicOpen g)
    (fun i : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i))
    (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{0} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
    hC hX hfet
  refine ⟨X.basicOpen g, hU₀.basicOpen g, (X.basicOpen_le g).trans hU₀U, hxU, m, c',
    fun i => (t i).down, fun i => ?_⟩
  rw [hc' (t i).down]
  show algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w (t i)) = _
  rw [hwt i]
  show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((X.presheaf.map (homOfLE hU₀U).op).hom (f i)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Establish `hcl : closure (S ∩ U) = closure S`. Apply `le_antisymm (closure_mono Set.inter_subset_left)` to reduce the goal to its premises. Conclude with `closure_minimal (subset_closure_inter_of_isPreirreducible_of_isOpen hS.2 hU h) isClosed_closure`. Conclude with `isIrreducible_iff_closure.mp (hcl ▸ hS.closure)`.
-/
theorem isIrreducible_inter_open' {Y : Type*} [TopologicalSpace Y] {S U : Set Y} (hS : IsIrreducible S)
    (hU : IsOpen U) (h : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  have hcl : closure (S ∩ U) = closure S := by
    apply le_antisymm (closure_mono Set.inter_subset_left)
    exact closure_minimal (subset_closure_inter_of_isPreirreducible_of_isOpen hS.2 hU h) isClosed_closure
  exact isIrreducible_iff_closure.mp (hcl ▸ hS.closure)

/- English proof (translation)
The claim follows from `le_antisymm (closure_minimal Set.inter_subset_left hSc) (subset_closure_inter_of_isPreirreducible_of_isOpen hS.2 hU h)`.
-/
theorem closure_inter_open_eq' {Y : Type*} [TopologicalSpace Y] {S U : Set Y} (hS : IsIrreducible S)
    (hSc : IsClosed S) (hU : IsOpen U) (h : (S ∩ U).Nonempty) : closure (S ∩ U) = S :=
  le_antisymm (closure_minimal Set.inter_subset_left hSc)
    (subset_closure_inter_of_isPreirreducible_of_isOpen hS.2 hU h)

/- English proof (translation)
Establish `h1 : y ∈ (c.coordIdeal {j}).support ↔ c.map.base y ∈ (coordSubspaceIdeal k m {j}).support`. Rewrite using `[EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Rewrite using `[h1, coordSubspaceIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span, Finset.coe_singleton, Set.image_singleton, Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe, not_iff_not]`. Establish `h2 : c.map.base y ∈ (affineSpaceFin k m).basicOpen (AffineSpace.coord (Spec (CommRingCat.of k)) ⟨j⟩) ↔ y ∈ c.map ⁻¹ᵁ (affineSpaceFin k m).basicOpen (AffineSpace.coord (Spec (CommRingCat.of k)) ⟨j⟩)` using `Iff.rfl`.

Rewrite using `[h2, Scheme.preimage_basicOpen_top]`. Use `(Scheme.Opens.mem_basicOpen_toScheme (U := U) (V := ⊤) (x := y)).trans ?_` and prove the remaining obligations. Rewrite using `[EtaleChart.coord_def]`. Simplify using `only [Scheme.Opens.topIso]`. Use `erw [Scheme.basicOpen_res]`.

Conclude with `⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩`.
-/
theorem mem_support_coordIdeal_singleton {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (j : Fin m) (y : U.toScheme) :
    y ∈ (c.coordIdeal {j}).support ↔ y.1 ∉ X.basicOpen (c.coord j) := by
  have h1 : y ∈ (c.coordIdeal {j}).support ↔ c.map.base y ∈ (coordSubspaceIdeal k m {j}).support := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← SetLike.mem_coe,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [h1, coordSubspaceIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Scheme.zeroLocus_span, Finset.coe_singleton, Set.image_singleton, Scheme.zeroLocus_singleton,
    Set.mem_compl_iff, SetLike.mem_coe, not_iff_not]
  have h2 : c.map.base y ∈ (affineSpaceFin k m).basicOpen
      (AffineSpace.coord (Spec (CommRingCat.of k)) ⟨j⟩) ↔
      y ∈ c.map ⁻¹ᵁ (affineSpaceFin k m).basicOpen (AffineSpace.coord (Spec (CommRingCat.of k)) ⟨j⟩) := Iff.rfl
  rw [h2, Scheme.preimage_basicOpen_top]
  refine (Scheme.Opens.mem_basicOpen_toScheme (U := U) (V := ⊤) (x := y)).trans ?_
  rw [EtaleChart.coord_def]
  simp only [Scheme.Opens.topIso]
  erw [Scheme.basicOpen_res]
  exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

/- English proof (translation)
Set `_ : Algebra (CoordPolynomialRing k m) Γ(Y, V)` to `c.algebra`. Establish `: Algebra.Etale (CoordPolynomialRing k m) Γ(Y, V)` using `c.algebra_etale hV`. Establish `h` using `isRadical_span_singleton_prod_etaleChartCoord k m Γ(Y, V) {j}`. Establish `hcoord : etaleChartCoord k m Γ(Y, V) j = c.coord j` using `by show c.coordRingHom (MvPolynomial.X (ULift.up j)) = c.coord j`. Conclude with `c.coordRingHom_X j`.

Rewrite `h` using `[Finset.prod_singleton, hcoord]`. Conclude with `h`.
-/
theorem isRadical_span_coord {Y : Scheme.{0}} {k : Type} [Field k] {q : Y ⟶ Spec (CommRingCat.of k)}
    {V : Y.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart q V m) (j : Fin m) :
    (Ideal.span {c.coord j}).IsRadical := by
  let _ : Algebra (CoordPolynomialRing k m) Γ(Y, V) := c.algebra
  have : Algebra.Etale (CoordPolynomialRing k m) Γ(Y, V) := c.algebra_etale hV
  have h := isRadical_span_singleton_prod_etaleChartCoord k m Γ(Y, V) {j}
  have hcoord : etaleChartCoord k m Γ(Y, V) j = c.coord j := by
    show c.coordRingHom (MvPolynomial.X (ULift.up j)) = c.coord j
    exact c.coordRingHom_X j
  rw [Finset.prod_singleton, hcoord] at h
  exact h

/- English proof (translation)
Use `Scheme.IdealSheafData.ext (funext fun V => ?_)` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.radical_ideal]`. Establish `e` using `c.coordIdeal_singleton_ideal_eq_span V.2 j`. Express the relevant statement in the definitionally equal form `((c.coordIdeal {j}).ideal ⟨V.1, V.2⟩).radical = (c.coordIdeal {j}).ideal ⟨V.1, V.2⟩`. Rewrite using `[e]`.

Conclude with `Ideal.radical_eq_iff.mpr (isRadical_span_coord V.2 (c.restrictOpens V.1) j)`.
-/
theorem radical_coordIdeal_singleton {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (j : Fin m) :
    (c.coordIdeal {j}).radical = c.coordIdeal {j} := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [Scheme.IdealSheafData.radical_ideal]
  have e := c.coordIdeal_singleton_ideal_eq_span V.2 j
  change ((c.coordIdeal {j}).ideal ⟨V.1, V.2⟩).radical = (c.coordIdeal {j}).ideal ⟨V.1, V.2⟩
  rw [e]
  exact Ideal.radical_eq_iff.mpr (isRadical_span_coord V.2 (c.restrictOpens V.1) j)

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `: TopologicalSpace.NoetherianSpace V.toScheme` using `inferInstance`. Set `D : V.toScheme.IdealSheafData` to `c.coordIdeal {t}`. Establish `hloc : ∀ y : V.toScheme, ∃ (U' : V.toScheme.Opens) (_ : y ∈ U') (n : ℕ) (c' : EtaleChart (V.ι ≫ p) U' n), restrictIdeal D U' = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U' = c'.coordIdeal {j}` using `fun y => ⟨⊤, trivial, m, c.restrictOpens ⊤, Or.inr ⟨t, c.restrictIdeal_coordIdeal ⊤ {t}⟩⟩`. Set `xt : V.toScheme` to `⟨x, hx⟩`.

Establish `hxs : xt ∈ (D.support : Set V.toScheme)` using `(mem_support_coordIdeal_singleton c t xt).mpr hxt`. Take `⟨K, hK, hxK⟩` from `exists_isIrreducibleComponentOfSupport D xt hxs`. Take `⟨V', -, hxV', n, c', j, -, hV'K, -⟩` from `hK.exists_affineOpen_etaleChart_coordIdeal (V.ι ≫ p) hloc xt hxK`. Set `N : X.Opens` to `⟨Subtype.val '' (V' : Set V.toScheme), V.isOpen.isOpenMap_subtype_val _ V'.isOpen⟩`. Use `⟨N, ?_, ⟨xt, hxV', rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨z, -, rfl⟩`. Conclude with `z.2`. Establish `hS : {y : X | y ∈ N ∧ y ∉ X.basicOpen (c.coord t)} = Subtype.val '' (K ∩ (V' : Set V.toScheme))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨z, hzV', rfl⟩, hzb⟩`. Establish `hzs : z ∈ (D.support : Set V.toScheme)` using `(mem_support_coordIdeal_singleton c t z).mpr hzb`. Conclude with `⟨z, ⟨hV'K z hzV' hzs, hzV'⟩, rfl⟩`. Introduce and unpack `⟨z, ⟨hzK, hzV'⟩, rfl⟩`. Conclude with `⟨⟨z, hzV', rfl⟩, (mem_support_coordIdeal_singleton c t z).mp (hK.subset_support hzK)⟩`.

Rewrite using `[hS]`. Conclude with `(isIrreducible_inter_open' hK.isIrreducible V'.isOpen ⟨xt, hxK, hxV'⟩).image _ continuous_subtype_val.continuousOn`.
-/
theorem exists_open_isIrreducible_zero {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    [IsNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) (t : Fin m) (x : X)
    (hx : x ∈ V) (hxt : x ∉ X.basicOpen (c.coord t)) :
    ∃ N : X.Opens, N ≤ V ∧ x ∈ N ∧ IsIrreducible ({y : X | y ∈ N ∧ y ∉ X.basicOpen (c.coord t)}) := by
  have : IsAffine V.toScheme := hV
  have : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  let D : V.toScheme.IdealSheafData := c.coordIdeal {t}
  have hloc : ∀ y : V.toScheme, ∃ (U' : V.toScheme.Opens) (_ : y ∈ U') (n : ℕ) (c' : EtaleChart (V.ι ≫ p) U' n),
      restrictIdeal D U' = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U' = c'.coordIdeal {j} :=
    fun y => ⟨⊤, trivial, m, c.restrictOpens ⊤, Or.inr ⟨t, c.restrictIdeal_coordIdeal ⊤ {t}⟩⟩
  let xt : V.toScheme := ⟨x, hx⟩
  have hxs : xt ∈ (D.support : Set V.toScheme) := (mem_support_coordIdeal_singleton c t xt).mpr hxt
  obtain ⟨K, hK, hxK⟩ := exists_isIrreducibleComponentOfSupport D xt hxs
  obtain ⟨V', -, hxV', n, c', j, -, hV'K, -⟩ := hK.exists_affineOpen_etaleChart_coordIdeal (V.ι ≫ p) hloc xt hxK
  let N : X.Opens := ⟨Subtype.val '' (V' : Set V.toScheme), V.isOpen.isOpenMap_subtype_val _ V'.isOpen⟩
  refine ⟨N, ?_, ⟨xt, hxV', rfl⟩, ?_⟩
  · rintro y ⟨z, -, rfl⟩
    exact z.2
  · have hS : {y : X | y ∈ N ∧ y ∉ X.basicOpen (c.coord t)} = Subtype.val '' (K ∩ (V' : Set V.toScheme)) := by
      ext y
      constructor
      · rintro ⟨⟨z, hzV', rfl⟩, hzb⟩
        have hzs : z ∈ (D.support : Set V.toScheme) := (mem_support_coordIdeal_singleton c t z).mpr hzb
        exact ⟨z, ⟨hV'K z hzV' hzs, hzV'⟩, rfl⟩
      · rintro ⟨z, ⟨hzK, hzV'⟩, rfl⟩
        exact ⟨⟨z, hzV', rfl⟩, (mem_support_coordIdeal_singleton c t z).mp (hK.subset_support hzK)⟩
    rw [hS]
    exact (isIrreducible_inter_open' hK.isIrreducible V'.isOpen ⟨xt, hxK, hxV'⟩).image _
      continuous_subtype_val.continuousOn

/- English proof (translation)
Set `Z : Fin m → Set X` to `fun t => (V : Set X) ∩ ((X.basicOpen (c.coord t) : X.Opens) : Set X)ᶜ`. Establish `hN : ∀ t : Fin m, ∃ N : X.Opens, N ≤ V ∧ x ∈ N ∧ (x ∈ Z t → IsIrreducible (Z t ∩ N)) ∧ (x ∉ Z t → Z t ∩ N = ∅)`. Introduce `t`. Distinguish the cases in `hxt : x ∈ X.basicOpen (c.coord t)`. Use `⟨X.basicOpen (c.coord t), X.basicOpen_le _, hxt, fun h => absurd hxt h.2, fun _ => ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Simplify using `only [Z, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]`. The claim follows by propositional logic. Take `⟨N, hNV, hxN, hirr⟩` from `exists_open_isIrreducible_zero hV c t x hx hxt`. Use `⟨N, hNV, hxN, fun _ => ?_, fun h => absurd ⟨hx, hxt⟩ h⟩` and prove the remaining obligations.

Use `hirr using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `only [Z, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, h1⟩, h2⟩`.

Conclude with `⟨h2, h1⟩`. Introduce and unpack `⟨h2, h1⟩`. Conclude with `⟨⟨hNV h2, h1⟩, h2⟩`. Use `choose N hNV hxN hNirr hNempty using hN`. Set `B : Set X` to `⋃ C ∈ 𝒞.filter (fun C : Closeds X => x ∉ C), (C : Set X)`.

Establish `hB : IsClosed B`. Use `Set.Finite.isClosed_biUnion (Finset.finite_toSet _) ?_` and prove the remaining obligations. Introduce `C _`. Conclude with `C.isClosed`. Establish `hxB : x ∉ B`.

Introduce `hx'`. Take `⟨C, hC, hxC⟩` from `Set.mem_iUnion₂.mp hx'`. Conclude with `(Finset.mem_filter.mp hC).2 hxC`. Set `W : X.Opens` to `⟨(V : Set X) ∩ (⋂ t, (N t : Set X)) ∩ Bᶜ, ((V.isOpen.inter (isOpen_iInter_of_finite fun t => (N t).isOpen)).inter hB.isOpen_compl)⟩`. Establish `hWV : W ≤ V` using `fun y hy => hy.1.1`.

Establish `hxW : x ∈ W` using `⟨⟨hx, Set.mem_iInter.mpr fun t => hxN t⟩, hxB⟩`. Establish `hWN : ∀ t, (W : Set X) ⊆ N t` using `fun t y hy => Set.mem_iInter.mp hy.1.2 t`. Establish `hEW : ∀ y ∈ W, y ∈ E ↔ ∃ t ∈ T, x ∈ Z t ∧ y ∈ Z t`. Introduce `y hy`. Rewrite using `[hE y (hWV hy)]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hyt⟩`. Use `⟨t, ht, ?_, ⟨hWV hy, hyt⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxt`. Establish `: y ∈ Z t ∩ N t` using `⟨⟨hWV hy, hyt⟩, hWN t hy⟩`.

Rewrite `this` using `[hNempty t hxt]`. Conclude with `this`. Introduce and unpack `⟨t, ht, -, hyt⟩`. Conclude with `⟨t, ht, hyt.2⟩`. Establish `hZirr : ∀ t, x ∈ Z t → IsIrreducible (Z t ∩ W)`.

Introduce `t hxt`. Establish `h` using `isIrreducible_inter_open' (hNirr t hxt) W.isOpen ⟨x, ⟨hxt, hxN t⟩, hxW⟩`. Establish `e : Z t ∩ N t ∩ W = Z t ∩ W`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, SetLike.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, -⟩, h3⟩`. Conclude with `⟨h1, h3⟩`. Introduce and unpack `⟨h1, h3⟩`. Conclude with `⟨⟨h1, hWN t h3⟩, h3⟩`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hcomp : ∀ C : Closeds X, C ∈ 𝒞 → x ∈ C → ∃ t, x ∈ Z t ∧ (C : Set X) ∩ W = Z t ∩ W`. Introduce `C hC hxC`. Establish `hCc` using `(h𝒞 C).1 hC`. Establish `hCW : IsIrreducible ((C : Set X) ∩ W)` using `isIrreducible_inter_open' hCc.1 W.isOpen ⟨x, hxC, hxW⟩`.

Establish `hcov : (C : Set X) ∩ W ⊆ ⋃₀ ↑((T.filter (fun t => x ∈ Z t)).image (fun t => ((X.basicOpen (c.coord t) : X.Opens) : Set X)ᶜ))`. Introduce and unpack `y ⟨hyC, hyW⟩`. Take `⟨t, ht, hxt, hyt⟩` from `(hEW y hyW).1 (hCc.2.1 hyC)`. Simplify using `only [Finset.coe_image, Finset.coe_filter, Set.sUnion_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]`. Conclude with `⟨t, ⟨ht, hxt⟩, hyt.2⟩`.

Take `⟨z, hz, hsub⟩` from `isIrreducible_iff_sUnion_isClosed.mp hCW _ (by`. Introduce `z hz`. Simplify using `only [Finset.mem_image] at hz`. Take `⟨t, -, rfl⟩` from `hz`. Conclude with `(X.basicOpen (c.coord t)).isOpen.isClosed_compl) hcov`.

Simplify using `only [Finset.mem_image, Finset.mem_filter] at hz`. Take `⟨t, ⟨ht, hxt⟩, rfl⟩` from `hz`. Use `⟨t, hxt, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `y hy`. Conclude with `⟨⟨hWV hy.2, hsub hy⟩, hy.2⟩`.

Establish `hS` using `hZirr t hxt`. Establish `hSE : Z t ∩ W ⊆ E`. Introduce `y hy`. Conclude with `(hEW y hy.2).2 ⟨t, ht, hxt, hy.1⟩`. Establish `hclE : closure (Z t ∩ W) ⊆ E` using `closure_minimal hSE E.isClosed`.

Establish `hCcl : (C : Set X) ⊆ closure (Z t ∩ W)`. Rewrite using `[← closure_inter_open_eq' hCc.1 C.isClosed W.isOpen ⟨x, hxC, hxW⟩]`. Conclude with `closure_mono (fun y hy => ⟨⟨hWV hy.2, hsub hy⟩, hy.2⟩)`. Use `hCc.2.2 _ hS.closure hclE hCcl` as an intermediate fact. Introduce `y hy`.

Conclude with `⟨this (subset_closure hy), hy.2⟩`. Set `lab : Closeds X → Option (Fin m)` to `fun C => if h : C ∈ 𝒞 ∧ x ∈ C then some (Classical.choose (hcomp C h.1 h.2)) else none`. Establish `hlab : ∀ C ∈ 𝒞, ∀ t, lab C = some t → x ∈ Z t ∧ (C : Set X) ∩ W = Z t ∩ W`. Introduce `C hC t ht`. Simplify using `only [lab] at ht`.

Use `split_ifs at ht with h`. Consider the cases of `ht`. Conclude with `Classical.choose_spec (hcomp C h.1 h.2)`. Establish `hlabx : ∀ C ∈ 𝒞, ∀ t, lab C = some t → x ∈ (C : Set X)`. Introduce `C hC t ht`.

Simplify using `only [lab] at ht`. Use `split_ifs at ht with h`. Conclude with `h.2`. Use `⟨W, hWV, hxW, lab, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `C hC C' hC' t h1 h2`.

Take `⟨-, e1⟩` from `hlab C hC t h1`. Take `⟨-, e2⟩` from `hlab C' hC' t h2`. Establish `hc1` using `(h𝒞 C).1 hC`. Establish `hc2` using `(h𝒞 C').1 hC'`. Apply `SetLike.coe_injective` to reduce the goal to its premises.

Rewrite using `[← closure_inter_open_eq' hc1.1 C.isClosed W.isOpen ⟨x, hlabx C hC t h1, hxW⟩, ← closure_inter_open_eq' hc2.1 C'.isClosed W.isOpen ⟨x, hlabx C' hC' t h2, hxW⟩, e1, e2]`. Introduce `C hC hnone`. Rewrite using `[restrictIdeal_eq_top_iff_forall_notMem_support]`. Introduce `y hyW hyC`. Establish `hyC' : y ∈ (C : Set X)`.

Rewrite `hyC` using `[← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Conclude with `hyC`. Establish `hxC : x ∉ (C : Set X)`. Introduce `hxC`. Establish `h' : lab C = some (Classical.choose (hcomp C hC hxC))` using `dif_pos ⟨hC, hxC⟩`.

Rewrite `hnone` using `[h']`. Consider the cases of `hnone`. Apply `hyW.2` to reduce the goal to its premises. Simplify using `only [B, Set.mem_iUnion, Finset.mem_filter, exists_prop]`. Conclude with `⟨C, ⟨hC, hxC⟩, hyC'⟩`.

Introduce `C hC t ht`. Take `⟨-, e⟩` from `hlab C hC t ht`. Rewrite using `[← radical_coordIdeal_singleton, ← Scheme.IdealSheafData.vanishingIdeal_support, restrictIdeal_eq_comap_ι]`. Use `comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq W.ι C _ ?_` and prove the remaining obligations. Use extensionality with `w`.

Rewrite using `[Set.mem_preimage]`. Express the relevant statement in the definitionally equal form `w ∈ ((c.restrict hWV).coordIdeal {t}).support ↔ w.1 ∈ (C : Set X)`. Rewrite using `[mem_support_coordIdeal_singleton, EtaleChart.coord_restrict, Scheme.basicOpen_res]`. Establish `hw : w.1 ∈ (C : Set X) ↔ w.1 ∈ Z t ∩ W`. Rewrite using `[← e]`.

Conclude with `⟨fun h => ⟨h, w.2⟩, fun h => h.1⟩`. Rewrite using `[hw]`. Simplify using `only [Z, Opens.mem_inf, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨⟨hWV w.2, fun h' => h ⟨w.2, h'⟩⟩, w.2⟩`. Introduce and unpack `⟨⟨-, h⟩, -⟩ ⟨-, h'⟩`. Conclude with `h h'`.
-/
theorem exists_labels {X : Scheme.{0}} {k : Type} [Field k] [CharZero k] {p : X ⟶ Spec (CommRingCat.of k)}
    [Smooth p] [IsNoetherian X] (E : Closeds X) (𝒞 : Finset (Closeds X))
    (h𝒞 : ∀ C : Closeds X, C ∈ 𝒞 ↔ IsCompOf (E : Set X) (C : Set X))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) (x : X) (hx : x ∈ V)
    (T : Finset (Fin m)) (hE : ∀ y ∈ V, y ∈ E ↔ ∃ t ∈ T, y ∉ X.basicOpen (c.coord t)) :
    ∃ (W : X.Opens) (hWV : W ≤ V) (_ : x ∈ W) (lab : Closeds X → Option (Fin m)),
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ t, lab C = some t → lab C' = some t → C = C') ∧
      (∀ C ∈ 𝒞, lab C = none → restrictIdeal (Scheme.IdealSheafData.vanishingIdeal C) W = ⊤) ∧
      (∀ C ∈ 𝒞, ∀ t, lab C = some t →
        restrictIdeal (Scheme.IdealSheafData.vanishingIdeal C) W = (c.restrict hWV).coordIdeal {t}) := by
  classical
  let Z : Fin m → Set X := fun t => (V : Set X) ∩ ((X.basicOpen (c.coord t) : X.Opens) : Set X)ᶜ
  have hN : ∀ t : Fin m, ∃ N : X.Opens, N ≤ V ∧ x ∈ N ∧ (x ∈ Z t → IsIrreducible (Z t ∩ N)) ∧
      (x ∉ Z t → Z t ∩ N = ∅) := by
    intro t
    by_cases hxt : x ∈ X.basicOpen (c.coord t)
    · refine ⟨X.basicOpen (c.coord t), X.basicOpen_le _, hxt, fun h => absurd hxt h.2, fun _ => ?_⟩
      ext y
      simp only [Z, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
      tauto
    · obtain ⟨N, hNV, hxN, hirr⟩ := exists_open_isIrreducible_zero hV c t x hx hxt
      refine ⟨N, hNV, hxN, fun _ => ?_, fun h => absurd ⟨hx, hxt⟩ h⟩
      convert hirr using 1
      ext y
      simp only [Z, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨⟨hNV h2, h1⟩, h2⟩
  choose N hNV hxN hNirr hNempty using hN
  let B : Set X := ⋃ C ∈ 𝒞.filter (fun C : Closeds X => x ∉ C), (C : Set X)
  have hB : IsClosed B := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) ?_
    intro C _
    exact C.isClosed
  have hxB : x ∉ B := by
    intro hx'
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx'
    exact (Finset.mem_filter.mp hC).2 hxC
  let W : X.Opens := ⟨(V : Set X) ∩ (⋂ t, (N t : Set X)) ∩ Bᶜ,
    ((V.isOpen.inter (isOpen_iInter_of_finite fun t => (N t).isOpen)).inter hB.isOpen_compl)⟩
  have hWV : W ≤ V := fun y hy => hy.1.1
  have hxW : x ∈ W := ⟨⟨hx, Set.mem_iInter.mpr fun t => hxN t⟩, hxB⟩
  have hWN : ∀ t, (W : Set X) ⊆ N t := fun t y hy => Set.mem_iInter.mp hy.1.2 t
  have hEW : ∀ y ∈ W, y ∈ E ↔ ∃ t ∈ T, x ∈ Z t ∧ y ∈ Z t := by
    intro y hy
    rw [hE y (hWV hy)]
    constructor
    · rintro ⟨t, ht, hyt⟩
      refine ⟨t, ht, ?_, ⟨hWV hy, hyt⟩⟩
      by_contra hxt
      have : y ∈ Z t ∩ N t := ⟨⟨hWV hy, hyt⟩, hWN t hy⟩
      rw [hNempty t hxt] at this
      exact this
    · rintro ⟨t, ht, -, hyt⟩
      exact ⟨t, ht, hyt.2⟩
  have hZirr : ∀ t, x ∈ Z t → IsIrreducible (Z t ∩ W) := by
    intro t hxt
    have h := isIrreducible_inter_open' (hNirr t hxt) W.isOpen ⟨x, ⟨hxt, hxN t⟩, hxW⟩
    have e : Z t ∩ N t ∩ W = Z t ∩ W := by
      ext y
      simp only [Set.mem_inter_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hWN t h3⟩, h3⟩
    rwa [e] at h
  have hcomp : ∀ C : Closeds X, C ∈ 𝒞 → x ∈ C → ∃ t, x ∈ Z t ∧ (C : Set X) ∩ W = Z t ∩ W := by
    intro C hC hxC
    have hCc := (h𝒞 C).1 hC
    have hCW : IsIrreducible ((C : Set X) ∩ W) := isIrreducible_inter_open' hCc.1 W.isOpen ⟨x, hxC, hxW⟩
    have hcov : (C : Set X) ∩ W ⊆ ⋃₀ ↑((T.filter (fun t => x ∈ Z t)).image
        (fun t => ((X.basicOpen (c.coord t) : X.Opens) : Set X)ᶜ)) := by
      rintro y ⟨hyC, hyW⟩
      obtain ⟨t, ht, hxt, hyt⟩ := (hEW y hyW).1 (hCc.2.1 hyC)
      simp only [Finset.coe_image, Finset.coe_filter, Set.sUnion_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨t, ⟨ht, hxt⟩, hyt.2⟩
    obtain ⟨z, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hCW _ (by
      intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact (X.basicOpen (c.coord t)).isOpen.isClosed_compl) hcov
    simp only [Finset.mem_image, Finset.mem_filter] at hz
    obtain ⟨t, ⟨ht, hxt⟩, rfl⟩ := hz
    refine ⟨t, hxt, le_antisymm ?_ ?_⟩
    · intro y hy
      exact ⟨⟨hWV hy.2, hsub hy⟩, hy.2⟩
    · have hS := hZirr t hxt
      have hSE : Z t ∩ W ⊆ E := by
        intro y hy
        exact (hEW y hy.2).2 ⟨t, ht, hxt, hy.1⟩
      have hclE : closure (Z t ∩ W) ⊆ E := closure_minimal hSE E.isClosed
      have hCcl : (C : Set X) ⊆ closure (Z t ∩ W) := by
        rw [← closure_inter_open_eq' hCc.1 C.isClosed W.isOpen ⟨x, hxC, hxW⟩]
        exact closure_mono (fun y hy => ⟨⟨hWV hy.2, hsub hy⟩, hy.2⟩)
      have := hCc.2.2 _ hS.closure hclE hCcl
      intro y hy
      exact ⟨this (subset_closure hy), hy.2⟩
  let lab : Closeds X → Option (Fin m) := fun C =>
    if h : C ∈ 𝒞 ∧ x ∈ C then some (Classical.choose (hcomp C h.1 h.2)) else none
  have hlab : ∀ C ∈ 𝒞, ∀ t, lab C = some t → x ∈ Z t ∧ (C : Set X) ∩ W = Z t ∩ W := by
    intro C hC t ht
    simp only [lab] at ht
    split_ifs at ht with h
    · cases ht
      exact Classical.choose_spec (hcomp C h.1 h.2)
  have hlabx : ∀ C ∈ 𝒞, ∀ t, lab C = some t → x ∈ (C : Set X) := by
    intro C hC t ht
    simp only [lab] at ht
    split_ifs at ht with h
    exact h.2
  refine ⟨W, hWV, hxW, lab, ?_, ?_, ?_⟩
  · intro C hC C' hC' t h1 h2
    obtain ⟨-, e1⟩ := hlab C hC t h1
    obtain ⟨-, e2⟩ := hlab C' hC' t h2
    have hc1 := (h𝒞 C).1 hC
    have hc2 := (h𝒞 C').1 hC'
    apply SetLike.coe_injective
    rw [← closure_inter_open_eq' hc1.1 C.isClosed W.isOpen ⟨x, hlabx C hC t h1, hxW⟩,
      ← closure_inter_open_eq' hc2.1 C'.isClosed W.isOpen ⟨x, hlabx C' hC' t h2, hxW⟩, e1, e2]
  · intro C hC hnone
    rw [restrictIdeal_eq_top_iff_forall_notMem_support]
    intro y hyW hyC
    have hyC' : y ∈ (C : Set X) := by
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hyC
      exact hyC
    have hxC : x ∉ (C : Set X) := by
      intro hxC
      have h' : lab C = some (Classical.choose (hcomp C hC hxC)) := dif_pos ⟨hC, hxC⟩
      rw [h'] at hnone
      cases hnone
    apply hyW.2
    simp only [B, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    exact ⟨C, ⟨hC, hxC⟩, hyC'⟩
  · intro C hC t ht
    obtain ⟨-, e⟩ := hlab C hC t ht
    rw [← radical_coordIdeal_singleton, ← Scheme.IdealSheafData.vanishingIdeal_support,
      restrictIdeal_eq_comap_ι]
    refine comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq W.ι C _ ?_
    ext w
    rw [Set.mem_preimage]
    change w ∈ ((c.restrict hWV).coordIdeal {t}).support ↔ w.1 ∈ (C : Set X)
    rw [mem_support_coordIdeal_singleton, EtaleChart.coord_restrict, Scheme.basicOpen_res]
    have hw : w.1 ∈ (C : Set X) ↔ w.1 ∈ Z t ∩ W := by
      rw [← e]; exact ⟨fun h => ⟨h, w.2⟩, fun h => h.1⟩
    rw [hw]
    simp only [Z, Opens.mem_inf, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · intro h; exact ⟨⟨hWV w.2, fun h' => h ⟨w.2, h'⟩⟩, w.2⟩
    · rintro ⟨⟨-, h⟩, -⟩ ⟨-, h'⟩; exact h h'

end PositivityTheory.ResPlug.GBnd

namespace PositivityTheory.ResPlug.GBnd

open FunctorialResolution FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_and, exists_false, imp_false]`. Consider the case `insert a J ha ih`. Rewrite using `[Finset.prod_insert ha, Scheme.basicOpen_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `h hyU`. Distinguish the cases in `h1 : y ∈ X.basicOpen (f a)`. Establish `h2 : y ∉ X.basicOpen (∏ i ∈ J, f i)` using `fun h2 => h ⟨h1, h2⟩`. Take `⟨i, hi, hyi⟩` from `ih.1 h2 hyU`.

Conclude with `⟨i, Finset.mem_insert_of_mem hi, hyi⟩`. Conclude with `⟨a, Finset.mem_insert_self a J, h1⟩`. Introduce and unpack `h ⟨h1, h2⟩`. Take `⟨i, hi, hyi⟩` from `h (X.basicOpen_le (f a) h1)`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases.

Conclude with `hyi h1`. Conclude with `ih.2 (fun _ => ⟨i, hi, hyi⟩) h2`.
-/
theorem notMem_basicOpen_prod_iff {X : Scheme.{0}} {U : X.Opens} {n : ℕ} (f : Fin n → Γ(X, U))
    (J : Finset (Fin n)) (y : X) :
    y ∉ X.basicOpen (∏ i ∈ J, f i) ↔ y ∈ U → ∃ i ∈ J, y ∉ X.basicOpen (f i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_and, exists_false,
      imp_false]
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    constructor
    · intro h hyU
      by_cases h1 : y ∈ X.basicOpen (f a)
      · have h2 : y ∉ X.basicOpen (∏ i ∈ J, f i) := fun h2 => h ⟨h1, h2⟩
        obtain ⟨i, hi, hyi⟩ := ih.1 h2 hyU
        exact ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
      · exact ⟨a, Finset.mem_insert_self a J, h1⟩
    · rintro h ⟨h1, h2⟩
      obtain ⟨i, hi, hyi⟩ := h (X.basicOpen_le (f a) h1)
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hyi h1
      · exact ih.2 (fun _ => ⟨i, hi, hyi⟩) h2

/- English proof (translation)
Establish `h0 : y ∈ E ↔ y ∈ (Scheme.IdealSheafData.vanishingIdeal E).support`. Rewrite using `[← SetLike.mem_coe, ← SetLike.mem_coe (x := y) (p := (Scheme.IdealSheafData.vanishingIdeal E).support), Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Rewrite using `[h0, PositivityTheory.ResPlug.BlowupCentre.mem_support_iff_forall_notMem_basicOpen _ U.2 hy]`. Establish `hU : (⟨U.1, U.2⟩ : X.affineOpens) = U` using `rfl`. Rewrite using `[hU, hid]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(notMem_basicOpen_prod_iff f J y).1 (h _ (Ideal.mem_span_singleton_self _)) hy`. Introduce `h g hg`. Rewrite `hg` using `[Ideal.mem_span_singleton]`.

Take `⟨a, rfl⟩` from `hg`. Introduce `hyg`. Rewrite `hyg` using `[Scheme.basicOpen_mul]`. Conclude with `(notMem_basicOpen_prod_iff f J y).2 (fun _ => h) hyg.1`.
-/
theorem mem_E_iff_of_ideal_eq {X : Scheme.{0}} (E : Closeds X) (U : X.affineOpens) {n : ℕ}
    (f : Fin n → Γ(X, U.1)) (J : Finset (Fin n))
    (hid : (Scheme.IdealSheafData.vanishingIdeal E).ideal U = Ideal.span {∏ i ∈ J, f i})
    (y : X) (hy : y ∈ U.1) : y ∈ E ↔ ∃ i ∈ J, y ∉ X.basicOpen (f i) := by
  have h0 : y ∈ E ↔ y ∈ (Scheme.IdealSheafData.vanishingIdeal E).support := by
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (x := y) (p := (Scheme.IdealSheafData.vanishingIdeal E).support),
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [h0, PositivityTheory.ResPlug.BlowupCentre.mem_support_iff_forall_notMem_basicOpen _ U.2 hy]
  have hU : (⟨U.1, U.2⟩ : X.affineOpens) = U := rfl
  rw [hU, hid]
  constructor
  · intro h
    exact (notMem_basicOpen_prod_iff f J y).1 (h _ (Ideal.mem_span_singleton_self _)) hy
  · intro h g hg
    rw [Ideal.mem_span_singleton] at hg
    obtain ⟨a, rfl⟩ := hg
    intro hyg
    rw [Scheme.basicOpen_mul] at hyg
    exact (notMem_basicOpen_prod_iff f J y).2 (fun _ => h) hyg.1

/- English proof (translation)
Distinguish the cases in `hx : x ∈ E`. Take `⟨-, U, hxU, n, f, J, hrsp, hid⟩` from `hE x hx`. Take `⟨V, hV, hVU, hxV, m, c, t, hct⟩` from `exists_chart_coords_of_rsp p U x hxU n f hrsp`. Use `⟨V, hV, hxV, m, c, J.image t, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_E_iff_of_ideal_eq E U f J hid y (hVU hy)]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, hyi⟩`. Use `⟨t i, Finset.mem_image_of_mem t hi, ?_⟩` and prove the remaining obligations. Rewrite using `[hct i, Scheme.basicOpen_res]`. Conclude with `fun h => hyi h.2`.

Introduce and unpack `⟨s, hs, hys⟩`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.mp hs`. Use `⟨i, hi, fun h => hys ?_⟩` and prove the remaining obligations. Rewrite using `[hct i, Scheme.basicOpen_res]`. Conclude with `⟨hy, h⟩`.

Set `W : X.Opens` to `⟨(E : Set X)ᶜ, E.2.isOpen_compl⟩`. Take `⟨U, m, hxU, hUW, hU, ⟨c⟩⟩` from `exists_etaleChart_le p x W hx`. Use `⟨U, hU, hxU, m, c, ∅, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.notMem_empty, false_and, exists_false, iff_false]`. Conclude with `hUW hy`.
-/
theorem exists_chart_E {X : Scheme.{0}} {k : Type} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (E : Closeds X)
    (hE : ∀ x ∈ E, FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal E) x) (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (m : ℕ) (c : EtaleChart p V m) (T : Finset (Fin m)),
      ∀ y ∈ V, y ∈ E ↔ ∃ t ∈ T, y ∉ X.basicOpen (c.coord t) := by
  classical
  by_cases hx : x ∈ E
  · obtain ⟨-, U, hxU, n, f, J, hrsp, hid⟩ := hE x hx
    obtain ⟨V, hV, hVU, hxV, m, c, t, hct⟩ := exists_chart_coords_of_rsp p U x hxU n f hrsp
    refine ⟨V, hV, hxV, m, c, J.image t, fun y hy => ?_⟩
    rw [mem_E_iff_of_ideal_eq E U f J hid y (hVU hy)]
    constructor
    · rintro ⟨i, hi, hyi⟩
      refine ⟨t i, Finset.mem_image_of_mem t hi, ?_⟩
      rw [hct i, Scheme.basicOpen_res]
      exact fun h => hyi h.2
    · rintro ⟨s, hs, hys⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      refine ⟨i, hi, fun h => hys ?_⟩
      rw [hct i, Scheme.basicOpen_res]
      exact ⟨hy, h⟩
  · let W : X.Opens := ⟨(E : Set X)ᶜ, E.2.isOpen_compl⟩
    obtain ⟨U, m, hxU, hUW, hU, ⟨c⟩⟩ := exists_etaleChart_le p x W hx
    refine ⟨U, hU, hxU, m, c, ∅, fun y hy => ?_⟩
    simp only [Finset.notMem_empty, false_and, exists_false, iff_false]
    exact hUW hy

/- English proof (translation)
Introduce `k _ _ X p _ _ _ E hE`. Establish `: IsNoetherian X` using `isNoetherian_of_locallyOfFiniteType p`. Take `⟨𝒞, h𝒞, hcov⟩` from `exists_finset_comps E`. Use `⟨𝒞.toList.map (fun C => Scheme.IdealSheafData.vanishingIdeal C), ?_, ?_⟩` and prove the remaining obligations. Apply `hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition` to reduce the goal to its premises.

Apply `inStrictNormalCrossingPosition_of_forall_etaleChart` to reduce the goal to its premises. Introduce `x`. Take `⟨V, hV, hxV, m, c, T, hET⟩` from `exists_chart_E p E hE x`. Take `⟨W, hWV, hxW, lab, h1, h2, h3⟩` from `exists_labels E 𝒞 h𝒞 hV c x hxV T hET`. Establish `hnd` using `𝒞.nodup_toList`.

Use `⟨W, hxW, m, c.restrict hWV, fun i => if h : i < 𝒞.toList.length then lab (𝒞.toList[i]'h) else none, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi i' hi' s hs hs'`. Simplify using `only [List.length_map] at hi hi'`. Simplify using `only at hs hs'`. Rewrite `hs` using `[dif_pos hi]`.

Rewrite `hs'` using `[dif_pos hi']`. Use `h1 _ (Finset.mem_toList.mp (List.getElem_mem hi)) _ (Finset.mem_toList.mp (List.getElem_mem hi')) s hs hs'` as an intermediate fact. Conclude with `(hnd.getElem_inj_iff).mp this`. Introduce `i hi hnone`. Simplify using `only [List.length_map] at hi`.

Simplify using `only at hnone`. Rewrite `hnone` using `[dif_pos hi]`. Simplify using `using h2 _ (Finset.mem_toList.mp (List.getElem_mem hi)) hnone`. Introduce `i hi s hs`. Simplify using `only [List.length_map] at hi`.

Simplify using `only at hs`. Rewrite `hs` using `[dif_pos hi]`. Simplify using `using h3 _ (Finset.mem_toList.mp (List.getElem_mem hi)) s hs`. Rewrite using `[← hcov]`. Use extensionality with `y`.

Simplify using `only [List.mem_map, Finset.mem_toList, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨D, ⟨C, hC, rfl⟩, hy⟩`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Then use the resulting hypothesis.

Introduce and unpack `⟨C, hC, hy⟩`. Use `⟨_, ⟨C, hC, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.coe_support_vanishingIdeal]` and apply the resulting hypothesis.
-/
theorem gBoundary : PositivityTheory.ResPlug.WeightsCompactStabilizer.GBoundary := by
  intro k _ _ X p _ _ _ E hE
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  obtain ⟨𝒞, h𝒞, hcov⟩ := exists_finset_comps E
  refine ⟨𝒞.toList.map (fun C => Scheme.IdealSheafData.vanishingIdeal C), ?_, ?_⟩
  · apply hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition
    apply inStrictNormalCrossingPosition_of_forall_etaleChart
    intro x
    obtain ⟨V, hV, hxV, m, c, T, hET⟩ := exists_chart_E p E hE x
    obtain ⟨W, hWV, hxW, lab, h1, h2, h3⟩ := exists_labels E 𝒞 h𝒞 hV c x hxV T hET
    have hnd := 𝒞.nodup_toList
    refine ⟨W, hxW, m, c.restrict hWV,
      fun i => if h : i < 𝒞.toList.length then lab (𝒞.toList[i]'h) else none, ?_, ?_, ?_⟩
    · intro i hi i' hi' s hs hs'
      simp only [List.length_map] at hi hi'
      dsimp only at hs hs'
      rw [dif_pos hi] at hs
      rw [dif_pos hi'] at hs'
      have := h1 _ (Finset.mem_toList.mp (List.getElem_mem hi)) _
        (Finset.mem_toList.mp (List.getElem_mem hi')) s hs hs'
      exact (hnd.getElem_inj_iff).mp this
    · intro i hi hnone
      simp only [List.length_map] at hi
      dsimp only at hnone
      rw [dif_pos hi] at hnone
      simpa using h2 _ (Finset.mem_toList.mp (List.getElem_mem hi)) hnone
    · intro i hi s hs
      simp only [List.length_map] at hi
      dsimp only at hs
      rw [dif_pos hi] at hs
      simpa using h3 _ (Finset.mem_toList.mp (List.getElem_mem hi)) s hs
  · rw [← hcov]
    ext y
    simp only [List.mem_map, Finset.mem_toList, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨D, ⟨C, hC, rfl⟩, hy⟩
      refine ⟨C, hC, ?_⟩
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy
    · rintro ⟨C, hC, hy⟩
      refine ⟨_, ⟨C, hC, rfl⟩, ?_⟩
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal]

end PositivityTheory.ResPlug.GBnd
