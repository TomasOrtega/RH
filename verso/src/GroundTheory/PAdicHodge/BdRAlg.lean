import Mathlib
import GroundTheory.PAdicHodge.ThetaPlus
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Ideal WittVector IsLocalRing

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := span {(p : S)}) inferInstance _ fun n => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `mem_span_singleton.1 (PadicInt.appr_spec n x)`. Establish `hx : x = (x.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * c` using `by rw [← hc]; ring`.

Establish `h : f x - g x = (p : S) ^ n * (f c - g c)`. Rewrite using `[hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[SModEq.zero, smul_eq_mul, mul_top, h, span_singleton_pow]`. Conclude with `Ideal.mul_mem_right _ _ (mem_span_singleton_self _)`.
-/
theorem ringHom_ext_padicInt {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S]
    [IsHausdorff (span {(p : S)}) S] (f g : ℤ_[p] →+* S) : f = g := by
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := span {(p : S)}) inferInstance _ fun n => ?_
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by rw [← hc]; ring
  have h : f x - g x = (p : S) ^ n * (f c - g c) := by
    rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, mul_top, h, span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _)

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔹" => BDeRhamPlus (normInteger K) p

def padicIntToWitt : ℤ_[p] →+* 𝕎𝒪♭ :=
  (WittVector.map (ZMod.castHom (dvd_refl p) 𝒪♭)).comp (WittVector.equiv p).symm.toRingHom

def padicIntToBDeRhamPlus : ℤ_[p] →+* 𝔹 :=
  (wittToBDeRhamPlus 𝒪 p).comp (padicIntToWitt p)

/- English proof (translation)
Establish `h` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : 𝕎𝒪♭)) (p : 𝕎𝒪♭)`. Establish `h2` using `h.map (toBDeRhamPlus 𝒪 p)`. Rewrite `h2` using `[map_natCast, map_natCast]`. Then use the resulting hypothesis.
-/
theorem isUnit_natCast_p_bDeRhamPlus : IsUnit (p : 𝔹) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : 𝕎𝒪♭)) (p : 𝕎𝒪♭)
  have h2 := h.map (toBDeRhamPlus 𝒪 p)
  rwa [map_natCast, map_natCast] at h2

/- English proof (translation)
Rewrite using `[PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]`. Conclude with `((PadicInt.unitCoeff hx).isUnit.map _).mul ((isUnit_natCast_p_bDeRhamPlus (K := K) p).pow _)`.
-/
theorem isUnit_padicIntToBDeRhamPlus {x : ℤ_[p]} (hx : x ≠ 0) :
    IsUnit (padicIntToBDeRhamPlus (K := K) p x) := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact ((PadicInt.unitCoeff hx).isUnit.map _).mul ((isUnit_natCast_p_bDeRhamPlus (K := K) p).pow _)

def padicToBDeRhamPlus : ℚ_[p] →+* 𝔹 :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) (g := padicIntToBDeRhamPlus (K := K) p)
    fun y => isUnit_padicIntToBDeRhamPlus (K := K) p (nonZeroDivisors.coe_ne_zero y)

instance algebraPadic : Algebra ℚ_[p] 𝔹 := (padicToBDeRhamPlus p).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_padic_eq : algebraMap ℚ_[p] 𝔹 = padicToBDeRhamPlus p := rfl

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) _ x`.
-/
theorem algebraMap_padic_coe (x : ℤ_[p]) :
    algebraMap ℚ_[p] 𝔹 (x : ℚ_[p]) = wittToBDeRhamPlus 𝒪 p (padicIntToWitt p x) :=
  IsLocalization.lift_eq (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) _ x

instance algebraRat : Algebra ℚ 𝔹 :=
  ((algebraMap ℚ_[p] 𝔹).comp (algebraMap ℚ ℚ_[p])).toAlgebra

instance isScalarTower_rat_padic : IsScalarTower ℚ ℚ_[p] 𝔹 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end IsPerfectoidField

section Cp

variable (p : ℕ) [Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

/- English proof (translation)
Rewrite using `[mem_normInteger, norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]`. Conclude with `x.norm_le_one`.
-/
theorem algebraMap_padicInt_mem_normInteger (x : ℤ_[p]) :
    algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) ∈ normInteger ℂ_[p] := by
  rw [mem_normInteger, norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
  exact x.norm_le_one

/- English proof (translation)
Set `g : ℤ_[p] →+* 𝒪` to `((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict _ (algebraMap_padicInt_mem_normInteger p)`. Use `IsPerfectoidField.isAdicComplete (K := ℂ_[p]) p` as an intermediate fact. Establish `h` using `ringHom_ext_padicInt ((fontaineTheta 𝒪 p).comp (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) g`. Conclude with `congrArg Subtype.val (RingHom.congr_fun h x)`.
-/
theorem fontaineTheta_padicIntToWitt (x : ℤ_[p]) :
    ((fontaineTheta 𝒪 p (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x) : 𝒪) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) := by
  let g : ℤ_[p] →+* 𝒪 :=
    ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict _
      (algebraMap_padicInt_mem_normInteger p)
  have := IsPerfectoidField.isAdicComplete (K := ℂ_[p]) p
  have h := ringHom_ext_padicInt ((fontaineTheta 𝒪 p).comp (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) g
  exact congrArg Subtype.val (RingHom.congr_fun h x)

/- English proof (translation)
Establish `h : (IsPerfectoidField.thetaBDeRhamPlusField p).comp (algebraMap ℚ_[p] 𝔹) = algebraMap ℚ_[p] ℂ_[p]`. Use `IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Establish `hx : algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p])` using `rfl`. Rewrite using `[hx, IsPerfectoidField.algebraMap_padic_coe, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, fontaineTheta_padicIntToWitt]`.

Conclude with `RingHom.congr_fun h q`.
-/
theorem thetaBDeRhamPlusField_algebraMap (q : ℚ_[p]) :
    IsPerfectoidField.thetaBDeRhamPlusField p (algebraMap ℚ_[p] 𝔹 q) = algebraMap ℚ_[p] ℂ_[p] q := by
  have h : (IsPerfectoidField.thetaBDeRhamPlusField p).comp (algebraMap ℚ_[p] 𝔹) =
      algebraMap ℚ_[p] ℂ_[p] := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    have hx : algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p]) := rfl
    rw [hx, IsPerfectoidField.algebraMap_padic_coe,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, fontaineTheta_padicIntToWitt]
  exact RingHom.congr_fun h q

def thetaAlgHom : 𝔹 →ₐ[ℚ_[p]] ℂ_[p] where
  toRingHom := IsPerfectoidField.thetaBDeRhamPlusField p
  commutes' := thetaBDeRhamPlusField_algebraMap p

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaAlgHom_apply (x : 𝔹) :
    thetaAlgHom p x = IsPerfectoidField.thetaBDeRhamPlusField p x := rfl

end Cp

end GroundTheory.PAdicHodge
