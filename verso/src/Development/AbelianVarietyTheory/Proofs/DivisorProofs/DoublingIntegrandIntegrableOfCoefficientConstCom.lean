import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
import Formalism.LocalToGlobal.IndefiniteReal.TopMult

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section
namespace GlobalTheory.RatioConst

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont Formalism.L2.Pj in

/- English proof (translation)
Simplify using `[GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]`.
-/
theorem rcoef_one_const {D : D7} {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    GlobalTheory.Core.Rk.IP.rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]

/- English proof (translation)
Introduce `D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0`. Establish `hF` using `hX.1`. Use `haveI := hF.haarA`. Use `set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef`. Establish `hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k`.

Introduce `g`. Take `⟨h, hh, k, hk, rfl⟩` from `Formalism.IndefR.TopMult.ga_decomp g`. Rewrite `hh` using `[← hF.rangeA]`. Take `⟨x, rfl⟩` from `hh`. Conclude with `⟨x, k, hk, rfl⟩`.

Establish `hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1`. Introduce `k hk v`. Use `show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1`. Rewrite using `[← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]`. Conclude with `GlobalTheory.AdelicU.proj_ofInf _ _ v _`.

Establish `hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1`. Introduce `k hk`. Simplify using `only [Lev.finE, MonoidHom.comp_apply]`. Rewrite using `[show finHom X.A k = 1 from hk, map_one]`. Establish `hmem : ∀ x k S, k ∈ GinfC X.A → (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S)`.

Introduce `x k S hk`. Simplify using `only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]`. Establish `hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g`. Introduce `g hg`. Take `⟨x, k, hk, rfl⟩` from `hdec g`.

Distinguish the cases in `hx : x ∈ intG D P.a`. Rewrite using `[Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]`. Rewrite using `[Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))), h0 x hx ((hmem x k Sf hk).1 hg) k hk]`. Establish `hKsub : K ⊆ openOff X.A (stdLat X.A) Sf` using `fun g hg v _ => hg v (Finset.notMem_empty v)`. Establish `hKm : MeasurableSet K` using `(GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet`.

Establish `hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf)` using `(GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet`. Establish `hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A))`. Use extensionality with `g`. Take `⟨x, k, hk, rfl⟩` from `hdec g`. Rewrite using `[SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]`.

Establish `hKvol : X.m K = 1`. Rewrite using `[hKeq]`. Conclude with `GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1`. Establish `hKc : IsCompact K`. Establish `hG : IsCompact (GinfC X.A : Set (GA D X.A))` using `GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA`.

Use `(hF.levA.2.mul hG).of_isClosed_subset ?_ ?_` and prove the remaining obligations. Rewrite using `[hKeq]`. Conclude with `Subgroup.isClosed_of_isOpen _ hF.levA.1`. Introduce `g hg`. Take `⟨x, k, hk, rfl⟩` from `hdec g`.

Rewrite `hg` using `[hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one]`. Use `Set.mul_mem_mul ?_ hk` and prove the remaining obligations. Conclude with `Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩`. Take `⟨hcont, hpos, -⟩` from `GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha`. Use `⟨fun s => ?_, ?_⟩` and prove the remaining obligations.

Set `F : GA D X.A → ℂ` to `fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g) (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)`. Establish `hFc : Continuous F`. Use `(continuous_const.mul ?_).mul continuous_const` and prove the remaining obligations. Simplify using `only [GlobalTheory.Doubling.npow]`. Use `(Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_` and prove the remaining obligations.

Conclude with `Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)`. Establish `hI : Integrable (K.indicator F) X.m` using `(integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)`. Use `hI.integrableOn.congr_fun (fun g hg => ?_) hSm` and prove the remaining obligations. Establish `hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ)`. Conclude with `rcoef_one_const X.m g`.

Simplify using `only [integrand, hr, hw g hg]`. Distinguish the cases in `hgK : g ∈ K`. Simplify using `[Set.indicator_of_mem hgK, F]`. Simplify using `[Set.indicator_of_notMem hgK]`. Rewrite using `[setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]`.

Simplify using the standard rewrite rules.
-/
theorem integral_const_coef : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  intro D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0
  have hF := hX.1
  haveI := hF.haarA
  set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef
  have hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k := by
    intro g
    obtain ⟨h, hh, k, hk, rfl⟩ := Formalism.IndefR.TopMult.ga_decomp g
    rw [← hF.rangeA] at hh
    obtain ⟨x, rfl⟩ := hh
    exact ⟨x, k, hk, rfl⟩
  have hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1 := by
    intro k hk v
    show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1
    rw [← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]
    exact GlobalTheory.AdelicU.proj_ofInf _ _ v _
  have hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1 := by
    intro k hk
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom X.A k = 1 from hk, map_one]
  have hmem : ∀ x k S, k ∈ GinfC X.A →
      (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S) := by
    intro x k S hk
    simp only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]
  have hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    by_cases hx : x ∈ intG D P.a
    · rw [Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]
    · rw [Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))),
        h0 x hx ((hmem x k Sf hk).1 hg) k hk]
  have hKsub : K ⊆ openOff X.A (stdLat X.A) Sf := fun g hg v _ => hg v (Finset.notMem_empty v)
  have hKm : MeasurableSet K := (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet
  have hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet
  have hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A)) := by
    ext g
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]
  have hKvol : X.m K = 1 := by
    rw [hKeq]; exact GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1
  have hKc : IsCompact K := by
    have hG : IsCompact (GinfC X.A : Set (GA D X.A)) :=
      GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA
    refine (hF.levA.2.mul hG).of_isClosed_subset ?_ ?_
    · rw [hKeq]; exact Subgroup.isClosed_of_isOpen _ hF.levA.1
    · intro g hg
      obtain ⟨x, k, hk, rfl⟩ := hdec g
      rw [hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one] at hg
      refine Set.mul_mem_mul ?_ hk
      exact Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩
  obtain ⟨hcont, hpos, -⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha
  refine ⟨fun s => ?_, ?_⟩
  · let F : GA D X.A → ℂ := fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g)
        (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)
    have hFc : Continuous F := by
      refine (continuous_const.mul ?_).mul continuous_const
      simp only [GlobalTheory.Doubling.npow]
      refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_
      exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)
    have hI : Integrable (K.indicator F) X.m :=
      (integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)
    refine hI.integrableOn.congr_fun (fun g hg => ?_) hSm
    have hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ) := by
      exact rcoef_one_const X.m g
    simp only [integrand, hr, hw g hg]
    by_cases hgK : g ∈ K
    · simp [Set.indicator_of_mem hgK, F]
    · simp [Set.indicator_of_notMem hgK]
  · rw [setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]
    simp

end GlobalTheory.RatioConst
