import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalCover

/- English proof (translation)
Take `⟨Ω, hne, hn⟩` from `GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety k X p D hX`. Use `hX.finite` as an intermediate fact. Establish `: IsFinite (spMap (Int.castRingHom k))` using `(IsFinite.SpecMap_iff _).2 (by`. Establish `: (Int.castRingHom k) = algebraMap ℤ k` using `RingHom.ext_int _ _`. Express the relevant statement in the definitionally equal form `(Int.castRingHom k).Finite`.

Rewrite using `[this]`. Conclude with `RingHom.finite_algebraMap.2 hX.finite)`. Establish `hs : IsProjOver (p ≫ spMap (Int.castRingHom k))`. Take `⟨h₁, h₂⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver`. Conclude with `(isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩`.

Use `hX.flat` as an intermediate fact. Take `⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩` from `GraphClosure.exists_normalisation_of_locallyClosed ℤ X Ω.toScheme (p ≫ spMap (Int.castRingHom k)) Ω (𝟙 _) hs inferInstance hn inferInstance`. Establish `he : IsOpenImmersion e` using `MorphismProperty.of_isPullback hpb.flip inferInstance`. Establish `: Nonempty Ω.toScheme` using `hne.to_subtype`. Establish `: IsIntegral Ω.toScheme` using `isIntegral_of_isOpenImmersion Ω.ι`.

Establish `: IsIntegral Y`. Use `GlobalTheory.IsNormalScheme.of_pred hnY` as an intermediate fact. Establish `h` using `((IrreducibleSpace.isIrreducible_univ Ω.toScheme).image _ e.continuous.continuousOn).closure`. Rewrite `h` using `[Set.image_univ, hd.closure_eq]`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def _).2 h`.

Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`. Establish `hfac : e ≫ ν = Ω.ι` using `by rw [hpb.w, Category.id_comp]`. Establish `hoi : IsOpenImmersion (e ≫ ν)` using `by rw [hfac]; infer_instance`. Establish `hg : e (genericPoint _) = genericPoint Y` using `genericPoint_eq_of_isOpenImmersion _`. Establish `hgen : ν (genericPoint Y) = genericPoint X`.

Rewrite using `[← hg, ← Scheme.Hom.comp_apply]`. Conclude with `genericPoint_eq_of_isOpenImmersion _`. Establish `hdeg : ν.residueDegree (genericPoint Y) ≠ 0`. Introduce `h0`. Establish `h1` using `CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)`.

Rewrite `h1` using `[CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul]`. Conclude with `one_ne_zero h1`. Establish `hproj : IsProjOver (ν ≫ p)` using `isProjOver_comp_of_isFinite ν hX.isProjOver`. Establish `hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom k))` using `by rwa [Category.assoc]`. Conclude with `⟨Y, ‹_›, ν, hν, hnY, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat, DimCover.topologicalKrullDim_eq k X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩, hgen, hdeg⟩`.
-/
theorem exists_normal_isArithVar (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ν : Y ⟶ X), IsFinite ν ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y ∧ IsArithVar (ν ≫ p) D ∧
      ν (genericPoint Y) = genericPoint X ∧ ν.residueDegree (genericPoint Y) ≠ 0 := by
  obtain ⟨Ω, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety k X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom k) = algebraMap ℤ k := RingHom.ext_int _ _
      change (Int.castRingHom k).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X Ω.toScheme
      (p ≫ spMap (Int.castRingHom k)) Ω (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty Ω.toScheme := hne.to_subtype
  have : IsIntegral Ω.toScheme := isIntegral_of_isOpenImmersion Ω.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ Ω.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = Ω.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom k)) := by rwa [Category.assoc]
  exact ⟨Y, ‹_›, ν, hν, hnY, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩,
    hgen, hdeg⟩

/- English proof (translation)
Introduce `k _ X p _ h` and use `exists_normal_isArithVar k X p 1 h`.
-/
theorem exists_normal_surface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X], IsArithVar p 1 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ν : Y ⟶ X),
      IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y ∧ IsArithVar (ν ≫ p) 1 ∧
      ν (genericPoint Y) = genericPoint X ∧ ν.residueDegree (genericPoint Y) ≠ 0 :=
  fun k _ X p _ h => exists_normal_isArithVar k X p 1 h

end GlobalTheory.NormalCover
