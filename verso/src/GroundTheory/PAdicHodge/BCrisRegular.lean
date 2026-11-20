import Mathlib
import GroundTheory.PAdicHodge.BCrisPlusInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section AwayLift

variable {R F : Type*} [CommRing R] [CommRing F] {t : R} (f : R →+* F) (ht : IsUnit (f t))

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ x`.
-/
theorem awayLift_algebraMap' (x : R) :
    Localization.awayLift f t ht (algebraMap R (Localization.Away t) x) = f x :=
  IsLocalization.lift_eq _ x

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨y, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers t) x`. Simplify using `only at hs`. Establish `h1` using `congrArg (Localization.awayLift f t ht) hs`.

Rewrite `h1` using `[map_mul, hx, zero_mul, awayLift_algebraMap']`. Establish `hy : y = 0` using `hf (by rw [map_zero]; exact h1.symm)`. Rewrite `hs` using `[hy, map_zero]`. Conclude with `(IsLocalization.map_units (Localization.Away t) s).mul_left_eq_zero.1 hs`.
-/
theorem awayLift_injective (hf : Function.Injective f) :
    Function.Injective (Localization.awayLift f t ht) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) x
  simp only at hs
  have h1 := congrArg (Localization.awayLift f t ht) hs
  rw [map_mul, hx, zero_mul, awayLift_algebraMap'] at h1
  have hy : y = 0 := hf (by rw [map_zero]; exact h1.symm)
  rw [hy, map_zero] at hs
  exact (IsLocalization.map_units (Localization.Away t) s).mul_left_eq_zero.1 hs

/- English proof (translation)
Establish `e : (Localization.awayLift f t ht).comp g = h.comp (Localization.awayLift f t ht)`. Apply `IsLocalization.ringHom_ext (Submonoid.powers t)` to reduce the goal to its premises. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[hgh, awayLift_algebraMap']`.

Conclude with `RingHom.congr_fun e z`.
-/
theorem awayLift_comp_eq (g : Localization.Away t →+* Localization.Away t) (h : F →+* F)
    (hgh : ∀ x : R, Localization.awayLift f t ht (g (algebraMap R (Localization.Away t) x)) =
      h (f x)) (z : Localization.Away t) :
    Localization.awayLift f t ht (g z) = h (Localization.awayLift f t ht z) := by
  have e : (Localization.awayLift f t ht).comp g = h.comp (Localization.awayLift f t ht) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [hgh, awayLift_algebraMap']
  exact RingHom.congr_fun e z

end AwayLift

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in

/- English proof (translation)
Rewrite using `[RingHom.comp_apply, iotaPlus_algebraMap, iota_periodT]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ))`.
-/
theorem isUnit_iotaPlus_periodT :
    IsUnit (((algebraMap 𝔹 𝔹dR).comp (iotaPlus ℂ_[p] p))
      (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε))) := by
  rw [RingHom.comp_apply, iotaPlus_algebraMap, iota_periodT]
  exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
    (fontaineT_ne_zero hε hζ))

def iotaB : BCris hε →+* 𝔹dR :=
  Localization.awayLift ((algebraMap 𝔹 𝔹dR).comp (iotaPlus ℂ_[p] p))
    (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) (isUnit_iotaPlus_periodT hε hζ)

/- English proof (translation)
The claim follows from `awayLift_algebraMap' _ (isUnit_iotaPlus_periodT hε hζ) x`.
-/
theorem iotaB_algebraMap (x : BCrisPlus ℂ_[p] p) :
    iotaB hε hζ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x) =
      algebraMap 𝔹 𝔹dR (iotaPlus ℂ_[p] p x) :=
  awayLift_algebraMap' _ (isUnit_iotaPlus_periodT hε hζ) x

/- English proof (translation)
The claim follows from `awayLift_injective _ (isUnit_iotaPlus_periodT hε hζ) ((IsFractionRing.injective 𝔹 𝔹dR).comp (iotaPlus_injective (K := ℂ_[p]) (p := p)))`.
-/
theorem iotaB_injective : Function.Injective (iotaB hε hζ) :=
  awayLift_injective _ (isUnit_iotaPlus_periodT hε hζ) ((IsFractionRing.injective 𝔹 𝔹dR).comp
    (iotaPlus_injective (K := ℂ_[p]) (p := p)))

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
The claim follows from `awayLift_comp_eq _ (isUnit_iotaPlus_periodT hε hζ) (galB hε σ) ((galBdRField σ : 𝔹dR ≃+* 𝔹dR) : 𝔹dR →+* 𝔹dR) (fun y => by rw [galB_algebraMap, awayLift_algebraMap', RingHom.comp_apply, RingHom.comp_apply, iotaPlus_gal_smul, RingHom.coe_coe, ← gal_smul_bDeRham_def, gal_smul_algebr …`.
-/
theorem iotaB_galB (σ : Gal(PadicAlgCl p/K)) (x : BCris hε) :
    iotaB hε hζ (galB hε σ x) = σ • iotaB hε hζ x :=
  awayLift_comp_eq _ (isUnit_iotaPlus_periodT hε hζ) (galB hε σ) ((galBdRField σ : 𝔹dR ≃+* 𝔹dR) : 𝔹dR →+* 𝔹dR)
    (fun y => by
      rw [galB_algebraMap, awayLift_algebraMap', RingHom.comp_apply, RingHom.comp_apply,
        iotaPlus_gal_smul, RingHom.coe_coe, ← gal_smul_bDeRham_def, gal_smul_algebraMap_bDeRham]) x

variable [FiniteDimensional ℚ_[p] K]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨k, hk⟩` from `bDeRham_fixed K (iotaB hε hζ x) fun σ => by rw [← iotaB_galB, hx σ]`. Conclude with `⟨k, hk.symm⟩`.
-/
theorem bCris_fixed (x : BCris hε) (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) :
    ∃ k : K, iotaB hε hζ x = algebraMap K 𝔹dR k := by
  obtain ⟨k, hk⟩ := bDeRham_fixed K (iotaB hε hζ x) fun σ => by rw [← iotaB_galB, hx σ]
  exact ⟨k, hk.symm⟩

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional ℚ_[p] K] in

/- English proof (translation)
Take `⟨x, hx, hxk⟩` from `exists_bCrisPlus_fixed hk`. Use `⟨algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x, fun σ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[galB_algebraMap]`. Conclude with `congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (hx σ)`. Rewrite using `[iotaB_algebraMap, hxk]`.
-/
theorem exists_bCris_fixed {k : PadicAlgCl p} (hk : k ∈ maxUnramified p K) :
    ∃ x : BCris hε, (∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) ∧
      iotaB hε hζ x = algebraMap 𝔹 𝔹dR (algClToBdR p k) := by
  obtain ⟨x, hx, hxk⟩ := exists_bCrisPlus_fixed hk
  refine ⟨algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x, fun σ => ?_, ?_⟩
  · rw [galB_algebraMap]
    exact congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (hx σ)
  · rw [iotaB_algebraMap, hxk]

end ACris

end GroundTheory.PAdicHodge
