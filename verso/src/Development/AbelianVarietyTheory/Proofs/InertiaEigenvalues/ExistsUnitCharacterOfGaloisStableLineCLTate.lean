import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

/- English proof (translation)
Use `choose x hx using h`. Establish `hn : ∀ g, ‖x g‖ = 1` using `fun g => by`. Establish `h1` using `GlobalTheory.RingBasics.norm_σC g y`. Rewrite `h1` using `[hx, norm_mul, norm_algebraMap']`. Conclude with `mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)`.

Establish `hm : ∀ g k, x (g * k) = x g * x k` using `fun g k => by`. Apply `(algebraMap ℚ_[l] ℂ_[l]).injective` to reduce the goal to its premises. Apply `mul_right_cancel₀ hy` to reduce the goal to its premises. Rewrite using `[← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hm g k`.
-/
theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
