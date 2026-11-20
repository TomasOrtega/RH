import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Mathlib.RingTheory.Valuation.LocalSubring

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 Polynomial
attribute [local instance] algMdl algPoly algRat

/- English proof (translation)
Use `letI := A.toAlgebra`. Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ (integralClosure R K).toSubring` using `hx`. Take `⟨V, hV, hxV⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx'`. Conclude with `hxV (h V fun r => hV ((integralClosure R K).algebraMap_mem r))`.
-/
private theorem valCrit {R K : Type} [CommRing R] [Field K] (A : R →+* K) (x : K)
    (h : ∀ V : ValuationSubring K, (∀ r, A r ∈ V) → x ∈ V) : A.IsIntegralElem x := by
  letI := A.toAlgebra
  by_contra hx
  have hx' : x ∉ (integralClosure R K).toSubring := hx
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx'
  exact hxV (h V fun r => hV ((integralClosure R K).algebraMap_mem r))

/- English proof (translation)
Introduce `Ω _ _ ε X M f hf`. Establish `key` using `valCrit ((topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M))) (f : X.K) (by`. Introduce `V hV`. Apply `hf V` to reduce the goal to its premises. Use `⟨fun c => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hV (Polynomial.C c)`. Express the relevant statement in the definitionally equal form `((jPoly X _ (Polynomial.C c) : X.K)) ∈ V at h1`. Rewrite `h1` using `[coe_jPoly, Polynomial.aeval_C]`. Then use the resulting hypothesis. Establish `h2` using `hV Polynomial.X`. Express the relevant statement in the definitionally equal form `((jPoly X _ Polynomial.X : X.K)) ∈ V at h2`.

Rewrite using `[coe_jPoly, Polynomial.aeval_X] at h2)` and apply the resulting hypothesis. Conclude with `RingHom.IsIntegralElem.of_map Subtype.val_injective key`.
-/
theorem UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : topL X M), (∀ W : ValuationSubring X.K, X.OverY W → (f : X.K) ∈ W) → f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  intro Ω _ _ ε X M f hf
  have key := valCrit ((topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M))) (f : X.K) (by
    intro V hV
    apply hf V
    refine ⟨fun c => ?_, ?_⟩
    · have h1 := hV (Polynomial.C c)
      change ((jPoly X _ (Polynomial.C c) : X.K)) ∈ V at h1
      rwa [coe_jPoly, Polynomial.aeval_C] at h1
    · have h2 := hV Polynomial.X
      change ((jPoly X _ Polynomial.X : X.K)) ∈ V at h2
      rwa [coe_jPoly, Polynomial.aeval_X] at h2)
  exact RingHom.IsIntegralElem.of_map Subtype.val_injective key
