import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.BlowSurf

/- English proof (translation)
Introduce `k _ T _ _ hT J hJ`. Take `⟨Y, b, hb, hproj, hiso⟩` from `ProjBlowup.exists_blowup (strHom k T) hT.isProjOver J`. Set `V : T.Opens` to `J.support.compl`. Establish `hbV : IsIso (b ∣_ V)` using `hiso V fun _ hx => hx`. Establish `: Nonempty V.toScheme` using `⟨⟨genericPoint T, hJ⟩⟩`.

Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`. Establish `: Nonempty (b ⁻¹ᵁ V).toScheme` using `⟨inv (b ∣_ V) (Classical.arbitrary _)⟩`. Establish `: IsIntegral (b ⁻¹ᵁ V).toScheme` using `isIntegral_of_isOpenImmersion (b ∣_ V)`. Establish `hU : (J.comap b).support.compl = b ⁻¹ᵁ V`. Use extensionality with `y`.

Conclude with `not_congr (ProjBlowup.mem_support_comap J b y)`. Establish `hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι` using `hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1`. Establish `: IsNoetherian Y` using `isNoetherian_of_isProjOver hproj`. Establish `: IsIntegral Y`. Establish `: IsReduced Y` using `IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι`.

Establish `h` using `((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _ (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure`. Rewrite `h` using `[Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range]`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def _).2 h`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`. Establish `hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι` using `(morphismRestrict_ι b V).symm`.

Establish `hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b)` using `by rw [hfac]; infer_instance`. Establish `hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y` using `genericPoint_eq_of_isOpenImmersion _`. Establish `hgen : b (genericPoint Y) = genericPoint T`. Rewrite using `[← hg, ← Scheme.Hom.comp_apply]`. Conclude with `genericPoint_eq_of_isOpenImmersion _`.

Use `letI : Algebra k Γ(Y, ⊤) := (b.appTop.hom.comp (algebraMap k Γ(T, ⊤))).toAlgebra`. Establish `hstr : b ≫ strHom k T = strHom k Y` using `comp_strHom (g := b) fun _ => rfl`. Establish `hlft : ∀ {R : Type} [CommRing R] (s : Y ⟶ Sp R), IsProjOver s → LocallyOfFiniteType s`. Introduce `R _ s hs`. Take `⟨n, i, hi, rfl⟩` from `hs`.

Use `isProper_str R n` as an intermediate fact. Use `infer_instance`. Establish `hlfT : LocallyOfFiniteType (strHom k T)`. Take `⟨n, i, hi, e⟩` from `hT.isProjOver`. Rewrite using `[← e]`.

Use `isProper_str k n` as an intermediate fact. Use `infer_instance`. Establish `hprojY : IsProjOver (strHom k Y)` using `hstr ▸ hproj`. Establish `hdim : topologicalKrullDim Y = 2`. Rewrite using `[OpenDim.topologicalKrullDim_eq_of_isIso_restrict k T Y (strHom k T) (strHom k Y) b hlfT (hlft _ hprojY) hstr V ⟨genericPoint T, hJ⟩ hbV, hT.dim_eq]`.

Establish `hdomb : IsDominant b` using `⟨by`. Rewrite using `[DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]`. Conclude with `closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩`. Establish `hst : IsIso (b.stalkMap (genericPoint Y))`. Establish `h1 : IsIso (((b ⁻¹ᵁ V).ι ≫ b).stalkMap (genericPoint _))` using `inferInstance`.

Rewrite `h1` using `[Scheme.Hom.stalkMap_comp]`. Establish `h3 : IsIso (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint (b ⁻¹ᵁ V).toScheme))` using `inferInstance`. Establish `h2 : IsIso (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _)))` using `@IsIso.of_isIso_comp_right _ _ _ _ _ (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _))) (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint _)) h3 h1`. Conclude with `hg ▸ h2`. Establish `hfin : IsGenFinite b 1`.

Use `⟨hdomb, one_pos, ?_⟩` and prove the remaining obligations. Use `letI := (b.stalkMap (genericPoint Y)).hom.toAlgebra`. Conclude with `Module.finrank_of_bijective_algebraMap (ConcreteCategory.bijective_of_isIso (b.stalkMap (genericPoint Y)))`. Conclude with `⟨Y, _, ‹_›, b, ⟨‹_›, hdim, hprojY⟩, hstr, hfin, hb.1⟩`.
-/
theorem exists_isProjSurface_effCartier : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ J : T.IdealSheafData, genericPoint T ∉ J.support → ∃ (T' : Scheme.{0}) (_ : Algebra k Γ(T', ⊤)) (_ : IsIntegral T') (ρ : T' ⟶ T), IsProjSurface k T' ∧ ρ ≫ strHom k T = strHom k T' ∧ IsGenFinite ρ 1 ∧ ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  intro k _ T _ _ hT J hJ
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup (strHom k T) hT.isProjOver J
  let V : T.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint T, hJ⟩⟩
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
  have hgen : b (genericPoint Y) = genericPoint T := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  letI : Algebra k Γ(Y, ⊤) := (b.appTop.hom.comp (algebraMap k Γ(T, ⊤))).toAlgebra
  have hstr : b ≫ strHom k T = strHom k Y := comp_strHom (g := b) fun _ => rfl
  have hlft : ∀ {R : Type} [CommRing R] (s : Y ⟶ Sp R), IsProjOver s → LocallyOfFiniteType s := by
    intro R _ s hs
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have hlfT : LocallyOfFiniteType (strHom k T) := by
    obtain ⟨n, i, hi, e⟩ := hT.isProjOver
    rw [← e]
    have := isProper_str k n
    infer_instance
  have hprojY : IsProjOver (strHom k Y) := hstr ▸ hproj
  have hdim : topologicalKrullDim Y = 2 := by
    rw [OpenDim.topologicalKrullDim_eq_of_isIso_restrict k T Y (strHom k T) (strHom k Y) b hlfT
      (hlft _ hprojY) hstr V ⟨genericPoint T, hJ⟩ hbV, hT.dim_eq]
  have hdomb : IsDominant b := ⟨by
    rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
  have hst : IsIso (b.stalkMap (genericPoint Y)) := by
    have h1 : IsIso (((b ⁻¹ᵁ V).ι ≫ b).stalkMap (genericPoint _)) := inferInstance
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h3 : IsIso (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint (b ⁻¹ᵁ V).toScheme)) := inferInstance
    have h2 : IsIso (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _))) :=
      @IsIso.of_isIso_comp_right _ _ _ _ _ (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _)))
        (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint _)) h3 h1
    exact hg ▸ h2
  have hfin : IsGenFinite b 1 := by
    refine ⟨hdomb, one_pos, ?_⟩
    letI := (b.stalkMap (genericPoint Y)).hom.toAlgebra
    exact Module.finrank_of_bijective_algebraMap
      (ConcreteCategory.bijective_of_isIso (b.stalkMap (genericPoint Y)))
  exact ⟨Y, _, ‹_›, b, ⟨‹_›, hdim, hprojY⟩, hstr, hfin, hb.1⟩

end GlobalTheory.BlowSurf
