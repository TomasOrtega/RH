import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponent
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipalSiegPreComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelIntegral

/- English proof (translation)
Introduce `X s _ U ⟨x, hx⟩`. Take `⟨a, ha, haU⟩` from `GlobalTheory.ConeOnto.exists_rat_pt s U.isOpen.isLocallyClosed hx`. Use `⟨a, ?_, haU⟩` and prove the remaining obligations. Rewrite using `[ha]`. Conclude with `(Spec.map_id _).symm`.
-/
theorem exists_complexPoint_mem : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] (U : X.Opens),
    (U : Set X).Nonempty → ∃ p : Sp ℂ ⟶ X, p ≫ s = spMap (RingHom.id ℂ) ∧ ∀ z : Sp ℂ, p z ∈ U := by
  intro X s _ U ⟨x, hx⟩
  obtain ⟨a, ha, haU⟩ := GlobalTheory.ConeOnto.exists_rat_pt s U.isOpen.isLocallyClosed hx
  refine ⟨a, ?_, haU⟩
  rw [ha]
  exact (Spec.map_id _).symm

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily`.
-/
theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k →
    Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ →
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, KeyFam.PtAt F.univ p τ := GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily

def conjEmb (n : ℕ) : cycAway n →+* ℂ := (starRingEnd ℂ).comp (cycAway n).subtype

/- English proof (translation)
The claim follows from `(RingHom.injective (starRingEnd ℂ)).comp Subtype.val_injective`.
-/
theorem conjEmb_injective (n : ℕ) : Function.Injective (conjEmb n) :=
  (RingHom.injective (starRingEnd ℂ)).comp Subtype.val_injective

/- English proof (translation)
Simplify using `only [conjEmb, RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, zetaAway, zeta]`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `[map_div₀, Complex.conj_ofReal, map_ofNat]`.
-/
theorem conjEmb_zeta (n : ℕ) :
    conjEmb n (zetaAway n) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := by
  simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, zetaAway, zeta]
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]

/- English proof (translation)
Establish `hL` using `GlobalTheory.abelianSchemeLaws_all`. Use `haveI := F.smooth`. Establish `: Smooth F.s` using `SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Rewrite using `[preconnectedSpace_iff_clopen]`. Introduce `W hW`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨p, hp, hpW⟩` from `exists_complexPoint_mem F.X F.s ⟨W, hW.isOpen⟩ hne.1`. Take `⟨q, hq, hqW⟩` from `exists_complexPoint_mem F.X F.s ⟨Wᶜ, hW.compl.isOpen⟩ (by simpa [Set.nonempty_compl] using hne.2)`. Establish `hζ : RingHom.id ℂ (conjEmb n (zetaAway n)) = Complex.exp (-(2 * Real.pi * Complex.I) / n)` using `conjEmb_zeta n`.

Take `⟨τ, hτ⟩` from `exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ p hp`. Take `⟨τ', hτ'⟩` from `exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ q hq`. Take `⟨hp', hq', H⟩` from `GlobalTheory.SiegelConnected.sameComp_of_ptAt hL.1 hL.2 GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ τ τ' p q hp hq hτ hτ'`. Take `⟨z⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Establish `h1` using `(pullback.fst F.s (spMap (RingHom.id ℂ))).continuous.image_connectedComponent_subset (pullback.lift q (𝟙 _) hq' z) ⟨_, H z, rfl⟩`.

Establish `e : ∀ (r : Sp ℂ ⟶ F.X) (hr : r ≫ F.s = 𝟙 _ ≫ spMap (RingHom.id ℂ)), pullback.fst F.s (spMap (RingHom.id ℂ)) (pullback.lift r (𝟙 _) hr z) = r z` using `fun r hr => by`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.lift_fst]`. Rewrite `h1` using `[e, e]`. Conclude with `hW.compl.connectedComponent_subset (hqW z) h1 (hpW z)`.
-/
theorem preconnected_of_complex (g n : ℕ) (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n)
    (F : SFam g n (conjEmb n (zetaAway n))) : PreconnectedSpace F.X := by
  have hL := GlobalTheory.abelianSchemeLaws_all
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  rw [preconnectedSpace_iff_clopen]
  intro W hW
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hpW⟩ := exists_complexPoint_mem F.X F.s ⟨W, hW.isOpen⟩ hne.1
  obtain ⟨q, hq, hqW⟩ := exists_complexPoint_mem F.X F.s ⟨Wᶜ, hW.compl.isOpen⟩
    (by simpa [Set.nonempty_compl] using hne.2)
  have hζ : RingHom.id ℂ (conjEmb n (zetaAway n)) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := conjEmb_zeta n
  obtain ⟨τ, hτ⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ p hp
  obtain ⟨τ', hτ'⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ q hq
  obtain ⟨hp', hq', H⟩ := GlobalTheory.SiegelConnected.sameComp_of_ptAt hL.1 hL.2 GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds
    g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ τ τ' p q hp hq hτ hτ'
  obtain ⟨z⟩ : Nonempty (Sp ℂ) := inferInstance
  have h1 := (pullback.fst F.s (spMap (RingHom.id ℂ))).continuous.image_connectedComponent_subset
    (pullback.lift q (𝟙 _) hq' z) ⟨_, H z, rfl⟩
  have e : ∀ (r : Sp ℂ ⟶ F.X) (hr : r ≫ F.s = 𝟙 _ ≫ spMap (RingHom.id ℂ)),
      pullback.fst F.s (spMap (RingHom.id ℂ)) (pullback.lift r (𝟙 _) hr z) = r z := fun r hr => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [e, e] at h1
  exact hW.compl.connectedComponent_subset (hqW z) h1 (hpW z)

end GlobalTheory.SiegelIntegral

open GlobalTheory.SiegelIntegral in

/- English proof (translation)
Introduce `g n hg hn hodd F`. Establish `hn0 : n ≠ 0` using `by omega`. Use `haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n`. Establish `hB : Geo.Tor.IsNormalScheme (Sp (cycAway n))` using `GlobalTheory.ZJ.isNormalScheme_sp _`. Use `haveI := F.smooth`.

Establish `: Smooth F.s` using `SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Establish `hN : Geo.Tor.IsNormalScheme F.X` using `GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension _ _ F.s (g * (g + 1) / 2) hB`. Use `haveI hLN : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s`. Use `⟨?_, hN, hLN⟩` and prove the remaining obligations. Use `haveI : GlobalTheory.IsNormalScheme F.X := GlobalTheory.IsNormalScheme.of_pred hN`.

Take `⟨F', π, hpb, -⟩` from `F.exists_baseChange (conjEmb n) (conjEmb_injective n) rfl`. Use `haveI := preconnected_of_complex g n hg hn hodd F'`. Establish `hgen : {x : F.X | (F.s x).asIdeal = ⊥} ⊆ Set.range π`. Introduce `x hx`. Establish `hx' : x ∈ Set.range (pullback.fst F.s (spMap (conjEmb n)))`.

Rewrite using `[Scheme.Pullback.range_fst]`. Use `⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(⊥ : Ideal ℂ).comap (conjEmb n) = (F.s x).asIdeal`. Rewrite using `[hx]`. Conclude with `Ideal.comap_bot_of_injective _ (conjEmb_injective n)`.

Take `⟨y, rfl⟩` from `hx'`. Conclude with `⟨hpb.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]⟩`. Establish `hpre : _root_.IsPreconnected (Set.univ : Set F.X)` using `(isPreconnected_range π.continuous).subset_closure (Set.subset_univ _) (by`. Rewrite using `[← F.isReduced_and_dense.2.closure_eq]`. Conclude with `closure_mono hgen)`.

Take `⟨c, hc, -⟩` from `GlobalTheory.exists_principal_siegPre_complex g n (Nat.pos_of_ne_zero hn0) (cycAway n) (cycAway n).subtype (zetaAway n) (Complex.isPrimitiveRoot_exp n hn0)`. Use `haveI := F.nonempty _ Subtype.val_injective c hc`. Use `haveI : ConnectedSpace F.X := { toPreconnectedSpace := ⟨hpre⟩, toNonempty := inferInstance }`. Conclude with `GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace F.X`.
-/
theorem GlobalTheory.SiegelIntegral.integral_normal_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  intro g n hg hn hodd F
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have hB : Geo.Tor.IsNormalScheme (Sp (cycAway n)) := GlobalTheory.ZJ.isNormalScheme_sp _
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  have hN : Geo.Tor.IsNormalScheme F.X :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension _ _ F.s (g * (g + 1) / 2) hB
  haveI hLN : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  refine ⟨?_, hN, hLN⟩
  haveI : GlobalTheory.IsNormalScheme F.X := GlobalTheory.IsNormalScheme.of_pred hN
  obtain ⟨F', π, hpb, -⟩ := F.exists_baseChange (conjEmb n) (conjEmb_injective n) rfl
  haveI := preconnected_of_complex g n hg hn hodd F'
  have hgen : {x : F.X | (F.s x).asIdeal = ⊥} ⊆ Set.range π := by
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst F.s (spMap (conjEmb n))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      change (⊥ : Ideal ℂ).comap (conjEmb n) = (F.s x).asIdeal
      rw [hx]
      exact Ideal.comap_bot_of_injective _ (conjEmb_injective n)
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨hpb.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]⟩
  have hpre : _root_.IsPreconnected (Set.univ : Set F.X) :=
    (isPreconnected_range π.continuous).subset_closure (Set.subset_univ _) (by
      rw [← F.isReduced_and_dense.2.closure_eq]
      exact closure_mono hgen)
  obtain ⟨c, hc, -⟩ := GlobalTheory.exists_principal_siegPre_complex g n (Nat.pos_of_ne_zero hn0) (cycAway n)
    (cycAway n).subtype (zetaAway n) (Complex.isPrimitiveRoot_exp n hn0)
  haveI := F.nonempty _ Subtype.val_injective c hc
  haveI : ConnectedSpace F.X := { toPreconnectedSpace := ⟨hpre⟩, toNonempty := inferInstance }
  exact GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace F.X
