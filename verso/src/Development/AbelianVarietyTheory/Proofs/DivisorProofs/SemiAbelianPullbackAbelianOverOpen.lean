import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorOverOpen

/- English proof (translation)
Introduce `x` and use `by obtain ⟨h₁, h₂⟩ := h x.1 have e := (V.stalkIso x).commRingCatIsoToRingEquiv exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩`.
-/
theorem isNormalScheme_opens {S : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (V : S.Opens) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

/- English proof (translation)
Establish `: CompactSpace V.toScheme` using `isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (V : Set S))`. Conclude with `{}`.
-/
theorem isNoetherian_opens {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (V : S.Opens) :
    AlgebraicGeometry.IsNoetherian V.toScheme := by
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (V : Set S))
  exact {}

/- English proof (translation)
Take `⟨i, hi, -⟩` from `grpPullback_iso hφ ((isGrpPullback_pullback G g).comp hψ)`. Conclude with `⟨_, ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G g)).congr (Category.id_comp _) rfl⟩`.
-/
theorem exists_isGrpPullback_cancel {S S' S'' : Scheme.{0}} {H : Over S} {G : Over S'} {A' : Over S''}
    [GrpObj H] [GrpObj G] [GrpObj A'] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ H.left} {ψ : G.left ⟶ H.left}
    (hφ : IsGrpPullback A' H (g ≫ f) φ) (hψ : IsGrpPullback G H f ψ) :
    ∃ φ' : A'.left ⟶ G.left, IsGrpPullback A' G g φ' := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso hφ ((isGrpPullback_pullback G g).comp hψ)
  exact ⟨_, ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G g)).congr (Category.id_comp _) rfl⟩

end GlobalTheory.FactorOverOpen

open GlobalTheory.FactorOverOpen in

/- English proof (translation)
Introduce `S X _ _ hS hX A _ hA H _ hH U₀ U hU₀ hU u' c A₀ _ e₀ e₁ h₀ h₁ K _ pt hpt hgen`. Set `V : S.Opens` to `U ⊓ U₀`. Establish `hη : ∀ W : S.Opens, (W : Set S).Nonempty → genericPoint S ∈ W` using `fun W hW => ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 (by simpa using hW)`. Establish `hηV : genericPoint S ∈ V` using `⟨hη U hU, hη U₀ hU₀⟩`. Use `haveI : Nonempty V := ⟨⟨_, hηV⟩⟩`.

Use `haveI : Nonempty U := ⟨⟨_, hη U hU⟩⟩`. Set `jU : V.toScheme ⟶ U.toScheme` to `S.homOfLE inf_le_left`. Set `j₀ : V.toScheme ⟶ U₀.toScheme` to `S.homOfLE inf_le_right`. Establish `hjU : jU ≫ U.ι = V.ι` using `S.homOfLE_ι _`. Establish `hj₀ : j₀ ≫ U₀.ι = V.ι` using `S.homOfLE_ι _`.

Establish `hrange : Set.range pt ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι, hpt]`. Simplify using `using hηV`. Set `z : Sp K ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι pt hrange`. Establish `hz : z ≫ V.ι = pt` using `IsOpenImmersion.lift_fac _ _ _`.

Use `haveI : IsDominant z := by`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[DenseRange, dense_iff_closure_eq, V.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp]`. Establish `: (⇑V.ι ∘ ⇑z) = ⇑pt` using `by rw [← hz]; rfl`. Rewrite using `[this, hpt, (genericPoint_spec S).def]`.

Both sides reduce to the same expression. Establish `ha : jU ≫ c = j₀ ≫ u'`. Use `ext_of_isDominant_of_isSeparated (ReciprocityTheory.ChartRestriction.G.Semi.toZ X) (specULiftZIsTerminal.hom_ext _ _) z ?_` and prove the remaining obligations. Use `hgen (z ≫ jU) (z ≫ j₀) (by rw [Category.assoc, hjU, hz]) (by rw [Category.assoc, hj₀, hz])` as an intermediate fact. Simplify `this` using `only [Category.assoc]`.

Set `G` to `(Over.pullback U.ι).obj H`. Set `G'` to `(Over.pullback c).obj A`. Establish `pH : IsGrpPullback ((Over.pullback j₀).obj A₀) H (jU ≫ U.ι) _` using `((isGrpPullback_pullback A₀ j₀).comp h₀).congr (hj₀.trans hjU.symm) rfl`. Establish `pA : IsGrpPullback ((Over.pullback j₀).obj A₀) A (jU ≫ c) _` using `((isGrpPullback_pullback A₀ j₀).comp h₁).congr ha.symm rfl`. Take `⟨φ, hφ⟩` from `exists_isGrpPullback_cancel pH (isGrpPullback_pullback H U.ι)`.

Take `⟨ψ, hψ⟩` from `exists_isGrpPullback_cancel pA (isGrpPullback_pullback A c)`. Use `haveI := isNoetherian_opens U`. Use `haveI : IsDominant jU := ⟨jU.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩`. Establish `hG : IsSemiAbelian G` using `IsSemiAbelian.pullback U.ι H hH`. Establish `hG' : IsSemiAbelian G'` using `IsSemiAbelian.pullback c A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)`.

Take `⟨E, ⟨hE, -⟩, -⟩` from `GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso_of_extensions GlobalTheory.semiAbelianHomExtension_holds (isNormalScheme_opens hS U) hG' hG hψ hφ`. Conclude with `⟨_, ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback H U.ι)).congr (Category.id_comp _) rfl⟩`.
-/
theorem GlobalTheory.FactorOverOpen.factor_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  intro S X _ _ hS hX A _ hA H _ hH U₀ U hU₀ hU u' c A₀ _ e₀ e₁ h₀ h₁ K _ pt hpt hgen

  let V : S.Opens := U ⊓ U₀
  have hη : ∀ W : S.Opens, (W : Set S).Nonempty → genericPoint S ∈ W := fun W hW =>
    ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 (by simpa using hW)
  have hηV : genericPoint S ∈ V := ⟨hη U hU, hη U₀ hU₀⟩
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty U := ⟨⟨_, hη U hU⟩⟩
  let jU : V.toScheme ⟶ U.toScheme := S.homOfLE inf_le_left
  let j₀ : V.toScheme ⟶ U₀.toScheme := S.homOfLE inf_le_right
  have hjU : jU ≫ U.ι = V.ι := S.homOfLE_ι _
  have hj₀ : j₀ ≫ U₀.ι = V.ι := S.homOfLE_ι _

  have hrange : Set.range pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hpt]
    simpa using hηV
  let z : Sp K ⟶ V.toScheme := IsOpenImmersion.lift V.ι pt hrange
  have hz : z ≫ V.ι = pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant z := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq,
      V.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp]
    have : (⇑V.ι ∘ ⇑z) = ⇑pt := by rw [← hz]; rfl
    rw [this, hpt, (genericPoint_spec S).def]
    rfl
  have ha : jU ≫ c = j₀ ≫ u' := by
    refine ext_of_isDominant_of_isSeparated (ReciprocityTheory.ChartRestriction.G.Semi.toZ X)
      (specULiftZIsTerminal.hom_ext _ _) z ?_
    have := hgen (z ≫ jU) (z ≫ j₀) (by rw [Category.assoc, hjU, hz]) (by rw [Category.assoc, hj₀, hz])
    simpa only [Category.assoc] using this

  let G := (Over.pullback U.ι).obj H
  let G' := (Over.pullback c).obj A
  have pH : IsGrpPullback ((Over.pullback j₀).obj A₀) H (jU ≫ U.ι) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₀).congr (hj₀.trans hjU.symm) rfl
  have pA : IsGrpPullback ((Over.pullback j₀).obj A₀) A (jU ≫ c) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₁).congr ha.symm rfl
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_cancel pH (isGrpPullback_pullback H U.ι)
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_cancel pA (isGrpPullback_pullback A c)

  haveI := isNoetherian_opens U
  haveI : IsDominant jU := ⟨jU.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG : IsSemiAbelian G := IsSemiAbelian.pullback U.ι H hH
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback c A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (isNormalScheme_opens hS U) hG' hG hψ hφ
  exact ⟨_, ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback H U.ι)).congr (Category.id_comp _) rfl⟩
