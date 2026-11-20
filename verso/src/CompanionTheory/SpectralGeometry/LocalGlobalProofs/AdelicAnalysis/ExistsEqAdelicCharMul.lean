import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CharDual

variable {F : Type} [Field F] [NumberField F]

def toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar (AF F) Circle where
  toFun x := ⟨ψ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact ψ.map_add_eq_mul a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : AF F) :
    ((toCircle ψ h x : Circle) : ℂ) = ψ x := rfl

/- English proof (translation)
The claim follows from `Continuous.subtype_mk hc _`.
-/
theorem continuous_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ) :
    Continuous (toCircle ψ h) :=
  Continuous.subtype_mk hc _

/- English proof (translation)
Take `⟨hc, hn, hF, x₀, hx₀⟩` from `hψ`. Take `⟨ξ, hξ, -⟩` from `GroundTheory.Global.existsUnique_eq_adelicChar_mul (toCircle ψ hn) (continuous_toCircle ψ hn hc) (fun k => Circle.ext (by simpa [coe_toCircle] using hF k))`. Establish `key : ∀ x : AF F, ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ)` using `fun x => by`. Rewrite using `[← hξ x, coe_toCircle]`. Use `⟨ξ, ?_, key⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Apply `hx₀` to reduce the goal to its premises. Rewrite using `[key x₀]`. Simplify using the standard rewrite rules.
-/
theorem exists_eq_adelicChar_mul (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ ξ : F, ξ ≠ 0 ∧ ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := by
  obtain ⟨hc, hn, hF, x₀, hx₀⟩ := hψ
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul (toCircle ψ hn)
    (continuous_toCircle ψ hn hc) (fun k => Circle.ext (by simpa [coe_toCircle] using hF k))
  have key : ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := fun x => by
    rw [← hξ x, coe_toCircle]
  refine ⟨ξ, ?_, key⟩
  rintro rfl
  apply hx₀
  rw [key x₀]
  simp

/- English proof (translation)
Take `⟨ξ, hξ0, hξ⟩` from `exists_eq_adelicChar_mul ψ hψ`. Take `⟨η, hη0, hη⟩` from `exists_eq_adelicChar_mul ψ' hψ'`. Use `⟨η / ξ, div_ne_zero hη0 hξ0, fun x => ?_⟩` and prove the remaining obligations. Establish `hc : ξ * (η / ξ) = η` using `by field_simp`. Rewrite using `[hη x, hξ, ← mul_assoc, ← map_mul, hc]`.
-/
theorem exists_scalar (ψ ψ' : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (hψ' : IsCharAF F ψ') :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_eq_adelicChar_mul ψ hψ
  obtain ⟨η, hη0, hη⟩ := exists_eq_adelicChar_mul ψ' hψ'
  refine ⟨η / ξ, div_ne_zero hη0 hξ0, fun x => ?_⟩
  have hc : ξ * (η / ξ) = η := by field_simp
  rw [hη x, hξ, ← mul_assoc, ← map_mul, hc]

end GlobalTheory.CompanionTheory.SW.CharDual

/- English proof (translation)
Introduce `_ _ _ ψ ψ' hψ hψ'` and use `GlobalTheory.CompanionTheory.SW.CharDual.exists_scalar ψ ψ' hψ hψ'`.
-/
theorem GlobalTheory.CompanionTheory.SW.char_dual : ∀ (F : Type) [Field F] [NumberField F] (ψ ψ' : AddChar (AF F) ℂ),
    IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) :=
  fun _ _ _ ψ ψ' hψ hψ' => GlobalTheory.CompanionTheory.SW.CharDual.exists_scalar ψ ψ' hψ hψ'
