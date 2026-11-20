import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPerImm

/- English proof (translation)
Introduce `A _ g L u _ U hU z hz w hw`. Use `GlobalTheory.HolUnifSec.eq_zero_of_fderiv_eq_zero u z w fun O f hO => ?_` and prove the remaining obligations. Establish `hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U` using `hz`. Establish `hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ O ⊓ U` using `(GlobalTheory.top_le_preimage_iff_mem _ _).1 ((GlobalTheory.top_le_preimage_inf _ O U).2 ⟨hO, hzU⟩)`. Take `⟨r, hrle, hrmem⟩` from `hU.exists_basicOpen_le (V := O ⊓ U) ⟨_, hmem⟩ hmem.2`.

Establish `hDO : A.left.basicOpen r ≤ O` using `hrle.trans inf_le_left`. Establish `hDU : A.left.basicOpen r ≤ U` using `A.left.basicOpen_le r`. Use `letI := (A.left.presheaf.map (homOfLE hDU).op).hom.toAlgebra`. Use `haveI := hU.isLocalization_basicOpen r`. Take `⟨n, b, hb⟩` from `IsLocalization.Away.surj r (resG A.left hDO f)`.

Set `P : Set (Fin g → ℂ)` to `{y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ A.left.basicOpen r}`. Establish `hP : IsOpen P` using `(u.hol _ 0).1`. Establish `hzP : z ∈ P` using `(GlobalTheory.top_le_preimage_iff_mem _ _).2 hrmem`. Use `set F := fun y => valAt' (u.ex y).left O f`. Use `set R := fun y => valAt' (u.ex y).left U r`.

Use `set B := fun y => valAt' (u.ex y).left U b`. Establish `key : ∀ y ∈ P, F y * R y ^ n = B y`. Introduce `y hy`. Establish `h1` using `congrArg (valAt' (u.ex y).left (A.left.basicOpen r)) hb`. Rewrite `h1` using `[GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hy]`.

Establish `e1 : valAt' (u.ex y).left (A.left.basicOpen r) (resG A.left hDO f) = F y` using `GlobalTheory.valAt'_res _ hDO f hy`. Establish `e2 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ r) = R y` using `GlobalTheory.valAt'_res _ hDU r hy`. Establish `e3 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ b) = B y` using `GlobalTheory.valAt'_res _ hDU b hy`. Rewrite `h1` using `[e1, e2, e3]`. Conclude with `h1`.

Establish `hpreO : IsOpen {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ O}` using `(u.hol O f).1`. Establish `hF : HasFDerivAt F (fderiv ℂ F z) z` using `(((u.hol O f).2 z hO).differentiableAt (hpreO.mem_nhds hO)).hasFDerivAt`. Establish `hR : HasFDerivAt R (fderiv ℂ R z) z` using `(((u.hol U r).2 z hzU).differentiableAt ((u.hol U r).1.mem_nhds hzU)).hasFDerivAt`. Establish `hB : HasFDerivAt B (fderiv ℂ B z) z` using `(((u.hol U b).2 z hzU).differentiableAt ((u.hol U b).1.mem_nhds hzU)).hasFDerivAt`. Establish `hFR` using `hF.mul (hR.pow n)`.

Establish `hev : (fun y => F y * R y ^ n) =ᶠ[nhds z] B` using `Filter.eventually_of_mem (hP.mem_nhds hzP) key`. Establish `hB'` using `hFR.congr_of_eventuallyEq hev.symm`. Establish `e` using `congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T w) (hB'.unique hB)`. Establish `hRw : fderiv ℂ R z w = 0` using `hw r`. Establish `hBw : fderiv ℂ B z w = 0` using `hw b`.

Establish `hRz : R z ≠ 0` using `(GlobalTheory.top_le_preimage_basicOpen_iff _ U r).1 hzP`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hRw, hBw, smul_zero, smul_eq_mul, mul_zero, zero_add] at e`. Conclude with `(mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hRz)`.
-/
theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ z ∈ pre u.ex U, ∀ w : Fin g → ℂ, (∀ b : Γ(A.left, U), fderiv ℂ (val u.ex U b) z w = 0) → w = 0 := by
  intro A _ g L u _ U hU z hz w hw
  refine GlobalTheory.HolUnifSec.eq_zero_of_fderiv_eq_zero u z w fun O f hO => ?_
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := hz
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ O ⊓ U :=
    (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((GlobalTheory.top_le_preimage_inf _ O U).2 ⟨hO, hzU⟩)
  obtain ⟨r, hrle, hrmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨_, hmem⟩ hmem.2
  have hDO : A.left.basicOpen r ≤ O := hrle.trans inf_le_left
  have hDU : A.left.basicOpen r ≤ U := A.left.basicOpen_le r
  letI := (A.left.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen r
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r (resG A.left hDO f)
  let P : Set (Fin g → ℂ) := {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ A.left.basicOpen r}
  have hP : IsOpen P := (u.hol _ 0).1
  have hzP : z ∈ P := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hrmem
  set F := fun y => valAt' (u.ex y).left O f
  set R := fun y => valAt' (u.ex y).left U r
  set B := fun y => valAt' (u.ex y).left U b
  have key : ∀ y ∈ P, F y * R y ^ n = B y := by
    intro y hy
    have h1 := congrArg (valAt' (u.ex y).left (A.left.basicOpen r)) hb
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hy] at h1
    have e1 : valAt' (u.ex y).left (A.left.basicOpen r) (resG A.left hDO f) = F y := GlobalTheory.valAt'_res _ hDO f hy
    have e2 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ r) = R y := GlobalTheory.valAt'_res _ hDU r hy
    have e3 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ b) = B y := GlobalTheory.valAt'_res _ hDU b hy
    rw [e1, e2, e3] at h1
    exact h1
  have hpreO : IsOpen {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ O} := (u.hol O f).1
  have hF : HasFDerivAt F (fderiv ℂ F z) z :=
    (((u.hol O f).2 z hO).differentiableAt (hpreO.mem_nhds hO)).hasFDerivAt
  have hR : HasFDerivAt R (fderiv ℂ R z) z :=
    (((u.hol U r).2 z hzU).differentiableAt ((u.hol U r).1.mem_nhds hzU)).hasFDerivAt
  have hB : HasFDerivAt B (fderiv ℂ B z) z :=
    (((u.hol U b).2 z hzU).differentiableAt ((u.hol U b).1.mem_nhds hzU)).hasFDerivAt
  have hFR := hF.mul (hR.pow n)
  have hev : (fun y => F y * R y ^ n) =ᶠ[nhds z] B :=
    Filter.eventually_of_mem (hP.mem_nhds hzP) key
  have hB' := hFR.congr_of_eventuallyEq hev.symm
  have e := congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T w) (hB'.unique hB)
  have hRw : fderiv ℂ R z w = 0 := hw r
  have hBw : fderiv ℂ B z w = 0 := hw b
  have hRz : R z ≠ 0 := (GlobalTheory.top_le_preimage_basicOpen_iff _ U r).1 hzP
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hRw, hBw, smul_zero, smul_eq_mul,
    mul_zero, zero_add] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hRz)

end GlobalTheory.CechPerImm
