import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Introduce `D`. Use `haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩`. Use `haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Set `φ : ↥D.LL0 →+* ℂ` to `D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)`. Establish `hφ : Function.Injective φ` using `φ.injective`.

Set `M` to `MonoidAlgebra.mapRangeRingHom (G0g D.nd) φ`. Establish `hM : Function.Injective M`. Introduce `x y h`. Use `MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)` and prove the remaining obligations. Use `congrArg (fun z => z.coeff g) h` as an intermediate fact.

Simplify `this` using `[M, MonoidAlgebra.mapRangeRingHom]`. Establish `he : M (eL D) = D.ntypes.e0`. Use `MonoidAlgebra.ext (Finsupp.ext fun g => ?_)` and prove the remaining obligations. Use `D.nStage_trivialCharacter_coeff_eq g` as an intermediate fact. Simplify `this` using `[M, eL, MonoidAlgebra.mapRangeRingHom, φ]`.

Establish `hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0` using `fun a => by`. Rewrite using `[← GlobalTheory.RowLev.ES_good]`. Conclude with `GlobalTheory.RowLev.ES_comm _ a`. Establish `hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0`. Rewrite using `[← GlobalTheory.RowLev.ES_good]`.

Conclude with `GlobalTheory.RowLev.ES_mul_self _`. Establish `hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g` using `fun g => by`. Simplify using `[M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom]`. Use `⟨hM ?_, fun g => hM ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, he, hi]`.

Rewrite using `[map_mul, map_mul, he, hs, hc]`.
-/
theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRangeRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRangeRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRangeRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
