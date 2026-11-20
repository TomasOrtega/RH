import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.CupGen.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTateTwistCupUnitAndPrimitiveRootClasses.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  first
  | exact @GlobalTheory.EtC.CupGen.main
  | exact GlobalTheory.EtC.CupGen.main
  | (intros; apply GlobalTheory.EtC.CupGen.main <;> assumption)
