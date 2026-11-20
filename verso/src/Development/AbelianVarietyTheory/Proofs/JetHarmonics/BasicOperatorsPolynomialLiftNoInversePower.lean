import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperatorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLifStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTermStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombinationStatement

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

/- English proof (translation)
Use `Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Rewrite `hh` using `[List.mem_singleton]`. Conclude with `hh ▸ hx`. Simplify using the standard rewrite rules.
-/
theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx`. Take `⟨y, -, h | h | h | h⟩` from `hx`. Conclude with `mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator Wp Wq P Bs X μ L st l0 d hD hN y)`. Conclude with `mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift Wp Wq P Bs X μ L st l0 d hD hN y)`. Conclude with `mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm Wp Wq P Bs X μ L st l0 d hD hN y)`.

Conclude with `mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polynomial_lift_dual_operator_combination Wp Wq P Bs X μ L st l0 d hD hN y)`.
-/
theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polynomial_lift_dual_operator_combination Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
