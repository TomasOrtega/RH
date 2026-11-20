import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.BlowArith

/- English proof (translation)
Use `hX.isNoetherianRing` as an intermediate fact. Take `⟨Y, b, hb, hproj, hiso⟩` from `ProjBlowup.exists_blowup p hX.isProjOver J`. Set `V : X.Opens` to `J.support.compl`. Establish `hbV : IsIso (b ∣_ V)` using `hiso V fun _ hx => hx`. Establish `: Nonempty V.toScheme` using `⟨⟨genericPoint X, hJ⟩⟩`.

Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`. Establish `: Nonempty (b ⁻¹ᵁ V).toScheme` using `⟨inv (b ∣_ V) (Classical.arbitrary _)⟩`. Establish `: IsIntegral (b ⁻¹ᵁ V).toScheme` using `isIntegral_of_isOpenImmersion (b ∣_ V)`. Establish `hU : (J.comap b).support.compl = b ⁻¹ᵁ V`. Use extensionality with `y`.

Conclude with `not_congr (ProjBlowup.mem_support_comap J b y)`. Establish `hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι` using `hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1`. Establish `: IsNoetherian Y` using `isNoetherian_of_isProjOver hproj`. Establish `: IsIntegral Y`. Establish `: IsReduced Y` using `IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι`.

Establish `h` using `((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _ (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure`. Rewrite `h` using `[Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range]`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def _).2 h`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`. Establish `hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι` using `(morphismRestrict_ι b V).symm`.

Establish `hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b)` using `by rw [hfac]; infer_instance`. Establish `hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y` using `genericPoint_eq_of_isOpenImmersion _`. Establish `hgen : b (genericPoint Y) = genericPoint X`. Rewrite using `[← hg, ← Scheme.Hom.comp_apply]`. Conclude with `genericPoint_eq_of_isOpenImmersion _`.

Establish `hdeg : b.residueDegree (genericPoint Y) ≠ 0`. Introduce `h0`. Establish `h1` using `CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)`. Rewrite `h1` using `[CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul]`. Conclude with `one_ne_zero h1`.

Establish `hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k))`. Rewrite using `[flat_int_iff_charZero]`. Use `hX.charZero` as an intermediate fact. Establish `: IsDominant b` using `⟨by`. Rewrite using `[DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]`.

Conclude with `closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩`. Use `IsSchemeTheoreticallyDominant.of_isDominant b` as an intermediate fact. Establish `hinj' : Function.Injective b.appTop` using `Scheme.Hom.app_injective b ⊤`. Conclude with `charZero_of_injective_ringHom (f := b.appTop.hom) hinj'`. Conclude with `⟨Y, b, ‹_›, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat, DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hgen, hdeg, hb.1⟩`.
-/
theorem exists_isArithVar_effCartier (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsArithVar (ρ ≫ p) D ∧
      ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0 ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ‹_›, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩,
    hgen, hdeg, hb.1⟩

end GlobalTheory.BlowArith
