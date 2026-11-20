import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.NormalGenSmooth

open GlobalTheory.RegGenSmooth

/- English proof (translation)
Establish `h1 : Ring.KrullDimLE 1 R` using `Ring.krullDimLE_iff.2 (by exact_mod_cast hd)`. Establish `h3 : IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _` using `⟨‹_›, fun P h0 hP => IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩`. Establish `: IsPrincipalIdealRing R` using `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 3).mpr h3`. Use `infer_instance`.
-/
theorem isRegularLocalRing_of_isIntegrallyClosed (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (hd : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  have h1 : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have h3 : IsIntegrallyClosed R ∧ ∀ P : Ideal R,
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨‹_›, fun P h0 hP => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 3).mpr h3
  infer_instance

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.charZero_base` as an intermediate fact. Establish `H` using `IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))`. Use `smoothOfRelativeDimension_genericFibre_of_affine k X p 1 fun A _ _ i _ hi => ?_` and prove the remaining obligations. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`.

Establish `hft : LocallyOfFiniteType (spMap (algebraMap k A))` using `by rw [← hi]; infer_instance`. Rewrite `hft` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `: Algebra.FiniteType k A` using `RingHom.finiteType_algebraMap.mp hft`. Use `smooth_of_regular _ _ 1 fun m hm => ?_` and prove the remaining obligations. Establish `hdim : ringKrullDim (Localization.AtPrime m) = (1 : ℕ)`.

Establish `: Nontrivial (FractionRing k ⊗[k] A)` using `Ideal.Quotient.nontrivial_iff.2 hm.ne_top |> fun _ => (Ideal.Quotient.mk m).domain_nontrivial`. Establish `: Nontrivial A`. Assume the negation of the conclusion as `hA`. Rewrite `hA` using `[not_nontrivial_iff_subsingleton]`. Conclude with `false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)`.

Take `⟨_, hd⟩` from `ringKrullDim_chart h H i hi`. Establish `e` using `height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m`. Rewrite `e` using `[hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm), add_zero]`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]`. Use `⟨?_, hdim⟩` and prove the remaining obligations.

Take `⟨i₀, _, -⟩` from `exists_affine_chart_of_isPullback H i hi`. Establish `: Flat (spMap (algebraMap k (FractionRing k)))` using `flat_specMap_localization (nonZeroDivisors k) _`. Establish `: IsPreimmersion (spMap (algebraMap k (FractionRing k)))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors k)`. Set `y : Spec (.of (FractionRing k ⊗[k] A))` to `(⟨m, inferInstance⟩ : PrimeSpectrum _)`. Use `GenSpread.isIso_stalkMap_of_flat (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)` as an intermediate fact.

Set `e : X.presheaf.stalk (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y)) ≃+* Localization.AtPrime m` to `(asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫ asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv`. Take `⟨h₁, h₂⟩` from `hn (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))`. Establish `: IsDomain (Localization.AtPrime m)` using `e.symm.toMulEquiv.isDomain _`. Establish `: IsIntegrallyClosed (Localization.AtPrime m)` using `IsIntegrallyClosed.of_equiv e`. Establish `: IsNoetherianRing (FractionRing k ⊗[k] A)` using `Algebra.FiniteType.isNoetherianRing (FractionRing k) _`.

Establish `: IsNoetherianRing (Localization.AtPrime m)` using `IsLocalization.isNoetherianRing m.primeCompl _ inferInstance`. Conclude with `isRegularLocalRing_of_isIntegrallyClosed _ (by rw [hdim]; norm_num)`.
-/
theorem smooth_genericFibre (h : IsArithVar p 1) (hn : Geo.Tor.IsNormalScheme X) :
    SmoothOfRelativeDimension 1 (pullback.snd p (spMap (algebraMap k (FractionRing k)))) := by
  have := h.isDomain
  have := h.charZero_base
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  refine smoothOfRelativeDimension_genericFibre_of_affine k X p 1 fun A _ _ i _ hi => ?_
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp hft
  refine smooth_of_regular _ _ 1 fun m hm => ?_
  have hdim : ringKrullDim (Localization.AtPrime m) = (1 : ℕ) := by
    have : Nontrivial (FractionRing k ⊗[k] A) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top |>
      fun _ => (Ideal.Quotient.mk m).domain_nontrivial
    have : Nontrivial A := by
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)
    obtain ⟨_, hd⟩ := ringKrullDim_chart h H i hi
    have e := height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m
    rw [hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm),
      add_zero] at e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]
  refine ⟨?_, hdim⟩
  obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
  have : Flat (spMap (algebraMap k (FractionRing k))) :=
    flat_specMap_localization (nonZeroDivisors k) _
  have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors k)
  let y : Spec (.of (FractionRing k ⊗[k] A)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have := GenSpread.isIso_stalkMap_of_flat
    (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)
  let e : X.presheaf.stalk (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y)) ≃+*
      Localization.AtPrime m :=
    (asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫
      asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv
  obtain ⟨h₁, h₂⟩ := hn (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))
  have : IsDomain (Localization.AtPrime m) := e.symm.toMulEquiv.isDomain _
  have : IsIntegrallyClosed (Localization.AtPrime m) := IsIntegrallyClosed.of_equiv e
  have : IsNoetherianRing (FractionRing k ⊗[k] A) := Algebra.FiniteType.isNoetherianRing (FractionRing k) _
  have : IsNoetherianRing (Localization.AtPrime m) := IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  exact isRegularLocalRing_of_isIntegrallyClosed _ (by rw [hdim]; norm_num)

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Use `h.isNoetherianRing` as an intermediate fact. Establish `: IsProper p` using `CommonModel.isProper_of_isProjOver h.isProjOver`. Establish `: LocallyOfFinitePresentation p` using `inferInstance`.

Use `smooth_genericFibre h hn` as an intermediate fact. Establish `H` using `IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))`. Establish `: Flat (spMap (algebraMap k (FractionRing k)))` using `flat_specMap_localization (nonZeroDivisors k) _`. Establish `: IsPreimmersion (spMap (algebraMap k (FractionRing k)))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors k)`. Take `⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ` from `⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by`.

Rewrite using `[RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩`. Establish `hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ`. Rewrite using `[← hτ, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))), y' ≫ pullback.fst _ _ = y.1` from `⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩`.

Take `⟨W, hW, hs⟩` from `GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H 1 (y' (IsLocalRing.closedPoint ℂ))`. Use `⟨W, mem_ptsIn.2 ?_, hs⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y.1 (IsLocalRing.closedPoint ℂ) ∈ W`. Rewrite using `[← hy']`. Conclude with `hW`.
-/
theorem exists_opens_smooth (h : IsArithVar p 1) (hn : Geo.Tor.IsNormalScheme X)
    (σ : k →+* ℂ) (y : CxPts p σ) :
    ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) := by
  have := h.isDomain
  have := h.finite
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : LocallyOfFinitePresentation p := inferInstance
  have := smooth_genericFibre h hn
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  have : Flat (spMap (algebraMap k (FractionRing k))) :=
    flat_specMap_localization (nonZeroDivisors k) _
  have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors k)
  obtain ⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ :=
    ⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ := by
    rw [← hτ, ← Spec.map_comp]
    rfl
  obtain ⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))),
      y' ≫ pullback.fst _ _ = y.1 :=
    ⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩
  obtain ⟨W, hW, hs⟩ := GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H 1
    (y' (IsLocalRing.closedPoint ℂ))
  refine ⟨W, mem_ptsIn.2 ?_, hs⟩
  change y.1 (IsLocalRing.closedPoint ℂ) ∈ W
  rw [← hy']
  exact hW

/- English proof (translation)
Introduce `_ _ _ _ h hn` and use `exists_opens_smooth h hn`.
-/
theorem exists_opens_smooth_of_isNormalScheme : ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsArithVar p 1 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) :=
  fun _ _ _ _ h hn => exists_opens_smooth h hn

end GlobalTheory.NormalGenSmooth
