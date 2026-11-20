import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CompletedStalk

/- English proof (translation)
Use `haveI : LocallyOfFiniteType M.s := M.lft`. Set `y : PrimeSpectrum o'` to `M.s x`. Use `letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y`. Use `haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ := StructureSheaf.IsLocalization.to_stalk _ y`. Set `φ` to `@algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A`.

Establish `h₁ : (M.s.stalkMap x).hom.EssFiniteType` using `LocallyOfFiniteType.stalkMap M.s x`. Establish `h₂ : φ.EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)`. Use `haveI : Algebra.FiniteType ℤ o' := hA.ft`. Establish `h₀ : (algebraMap ℤ o').EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 inferInstance`. Establish `h` using `((h₀.comp h₂).comp h₁)`.

Rewrite using `[← RingHom.essFiniteType_algebraMap]`. Use `h` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`.
-/
theorem essFiniteType_int_stalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.Poinc.CompletedStalk

/- English proof (translation)
Introduce `o' Ω _ _ _ hA S ρ hB M U₀ EE FinalForm hAdm hEE x hx`. Establish `hinjΩ` using `M.stalkHom_injective x`. Use `haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain`. Use `haveI : CharZero Ω := hA.char`. Use `haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance`.

Use `haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hAdm.1.normal x).2`. Use `haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x`. Use `haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _`. Establish `fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG` using `IsNoetherian.noetherian _`. Use `haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) := AdicCompletion.isLocalRing_of_fg fg`.

Take `⟨hRd, hRi⟩` from `GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)`. Use `haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _`. Establish `hm` using `AdicCompletion.maximalIdeal_eq_map_of_fg fg`. Use `set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR`. Use `set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ`.

Establish `hcpl : IsAdicComplete (maximalIdeal R) R`. Rewrite using `[hm]`. Conclude with `AdicCompletion.isAdicComplete_self _ fg`. Establish `hinj : Function.Injective φ` using `AdicCompletion.of_injective _ _`. Use `haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance`.

Use `set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ`. Establish `hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty`. Set `w : Sp R` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. Set `p : Sp (M.Z.presheaf.stalk x)` to `spMap φ w`. Establish `hp : p.asIdeal = ⊥` using `by show Ideal.comap φ ⊥ = ⊥`.

Rewrite using `[← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot φ).1 hinj`. Establish `hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `genericPoint_specializes x`.

Take `⟨q, hq⟩` from `hgen`. Establish `hpq : p ⤳ q` using `(PrimeSpectrum.le_iff_specializes p q).1 (by show p.asIdeal ≤ q.asIdeal`. Rewrite using `[hp]`. Conclude with `bot_le)`. Establish `hsp : ξ w ⤳ genericPoint M.Z`.

Use `hpq.map (M.Z.fromSpecStalk x).continuous` as an intermediate fact. Rewrite `this` using `[hq]`. Conclude with `this`. Use `⟨w, ?_⟩` and prove the remaining obligations. Use `show ξ w ∈ abLocus FinalForm.G`.

Rewrite using `[FinalForm.ab]`. Conclude with `le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)`. Use `haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj`. Take `⟨D, A, U, hL, hP⟩` from `FinalForm.unif R hRn hRi hcpl ξ hne`. Conclude with `⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance, pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, isGrpPullback_pullback _ _, hL, hP⟩`.
-/
theorem GlobalTheory.Poinc.CompletedStalk.exists_completion_unif : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧ ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  intro o' Ω _ _ _ hA S ρ hB M U₀ EE FinalForm hAdm hEE x hx
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hAdm.1.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _,
    isGrpPullback_pullback _ _, hL, hP⟩
