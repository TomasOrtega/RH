import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

/- English proof (translation)
Take `⟨⟨a, b⟩, hx⟩` from `IsLocalization.surj (nonZeroDivisors R) (x : K)`. Establish `hb : algebraMap R K (b : R) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Establish `hS : x * algebraMap R S (b : R) = algebraMap R S a`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hx`.

Establish `hu : u x * algebraMap R K (b : R) = algebraMap R K a`. Simplify `congrArg u hS` using `only [map_mul, AlgHom.commutes]`. Conclude with `mul_right_cancel₀ hb (hu.trans hx.symm)`.
-/
theorem algHom_eq_val {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) (u : S →ₐ[R] K) (x : S) : u x = x := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) (x : K)
  have hb : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hS : x * algebraMap R S (b : R) = algebraMap R S a := by
    apply Subtype.ext
    simpa using hx
  have hu : u x * algebraMap R K (b : R) = algebraMap R K a := by
    simpa only [map_mul, AlgHom.commutes] using congrArg u hS
  exact mul_right_cancel₀ hb (hu.trans hx.symm)

/- English proof (translation)
Use `haveI hepi : Epi (CommRingCat.ofHom (algebraMap R A)) := ⟨fun g h e => CommRingCat.hom_ext (IsLocalization.ringHom_ext M (by`. Simplify using `using congrArg CommRingCat.Hom.hom e))⟩`. Use `haveI hsp : Mono (spMap (algebraMap R A)) := (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))`. Use `infer_instance`.
-/
theorem mono_fst_localization {R : Type} [CommRing R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization M A] {B : Scheme.{0}} (pB : B ⟶ Sp R) :
    Mono (pullback.fst pB (spMap (algebraMap R A))) := by
  haveI hepi : Epi (CommRingCat.ofHom (algebraMap R A)) :=
    ⟨fun g h e => CommRingCat.hom_ext (IsLocalization.ringHom_ext M (by
      simpa using congrArg CommRingCat.Hom.hom e))⟩
  haveI hsp : Mono (spMap (algebraMap R A)) :=
    (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))
  infer_instance

end GenericLB

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ B pB M hqc hqs hM`. Use `haveI := hqc`. Use `haveI := hqs`. Take `⟨s, M₀, hM₀, -, hfac⟩` from `LBLimit.exists_lb_of_isLimit (Spread.bcDiagram pB K) (fun i => (Spread.bcCone pB K).π.app i) (fun g => (Spread.bcCone pB K).w g) (Spread.isLimitBcCone pB K) M hM`. Take `⟨f, hf0, hlift⟩` from `GenericLB.exists_denom (R := R) (K := K) s.unop`.

Take `⟨ψ, hψ⟩` from `hlift (Localization.Away f) (algebraMap R (Localization.Away f)) (IsLocalization.Away.algebraMap_isUnit f)`. Set `ψa : Algebra.adjoin R (s.unop : Set K) →ₐ[R] Localization.Away f` to `{ ψ with commutes' := fun r => RingHom.congr_fun hψ r }`. Use `⟨f, hf0, M₀.pull (Spread.bcMap pB ψa), pull_isLB hM₀ _, fun jm hjm => ?_⟩` and prove the remaining obligations. Establish `hfK : IsUnit (algebraMap R K f)` using `isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf0))`. Set `χ : Localization.Away f →ₐ[R] K` to `{ IsLocalization.Away.lift f hfK with commutes' := fun r => IsLocalization.lift_eq _ r }`.

Use `haveI := GenericLB.mono_fst_localization (Submonoid.powers f) (Localization.Away f) pB`. Establish `hj : jm = Spread.bcMap pB χ`. Rewrite using `[← cancel_mono (pullback.fst pB (spMap (algebraMap R (Localization.Away f)))), hjm, Spread.bcMap_fst]`. Establish `hcomp : jm ≫ Spread.bcMap pB ψa = (Spread.bcCone pB K).π.app s`. Rewrite using `[hj, Spread.bcMap_comp]`.

Use `show _ = Spread.bcMap pB (Algebra.adjoin R (s.unop : Set K)).val`. Use `congr 1`. Conclude with `AlgHom.ext fun x => GenericLB.algHom_eq_val _ _ x`. Conclude with `hfac _ jm (Spread.bcMap pB ψa) hcomp`.
-/
theorem lb_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  intro R K _ _ _ _ _ _ B pB M hqc hqs hM
  classical
  haveI := hqc
  haveI := hqs
  obtain ⟨s, M₀, hM₀, -, hfac⟩ := LBLimit.exists_lb_of_isLimit (Spread.bcDiagram pB K)
    (fun i => (Spread.bcCone pB K).π.app i) (fun g => (Spread.bcCone pB K).w g)
    (Spread.isLimitBcCone pB K) M hM
  obtain ⟨f, hf0, hlift⟩ := GenericLB.exists_denom (R := R) (K := K) s.unop
  obtain ⟨ψ, hψ⟩ := hlift (Localization.Away f) (algebraMap R (Localization.Away f))
    (IsLocalization.Away.algebraMap_isUnit f)
  let ψa : Algebra.adjoin R (s.unop : Set K) →ₐ[R] Localization.Away f :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  refine ⟨f, hf0, M₀.pull (Spread.bcMap pB ψa), pull_isLB hM₀ _, fun jm hjm => ?_⟩
  have hfK : IsUnit (algebraMap R K f) :=
    isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0))
  let χ : Localization.Away f →ₐ[R] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => IsLocalization.lift_eq _ r }
  haveI := GenericLB.mono_fst_localization (Submonoid.powers f) (Localization.Away f) pB
  have hj : jm = Spread.bcMap pB χ := by
    rw [← cancel_mono (pullback.fst pB (spMap (algebraMap R (Localization.Away f)))), hjm,
      Spread.bcMap_fst]
  have hcomp : jm ≫ Spread.bcMap pB ψa = (Spread.bcCone pB K).π.app s := by
    rw [hj, Spread.bcMap_comp]
    show _ = Spread.bcMap pB (Algebra.adjoin R (s.unop : Set K)).val
    congr 1
    exact AlgHom.ext fun x => GenericLB.algHom_eq_val _ _ x
  exact hfac _ jm (Spread.bcMap pB ψa) hcomp

end GlobalTheory
