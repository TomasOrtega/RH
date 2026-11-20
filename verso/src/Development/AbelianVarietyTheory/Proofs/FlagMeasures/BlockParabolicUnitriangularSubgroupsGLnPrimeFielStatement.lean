import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBlockParabolicUnitriangularSubgroupsGLnPrimeFiel.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  first | exact @GlobalTheory.GLm.ParBasic.par_basic | exact GlobalTheory.GLm.ParBasic.par_basic | (intros; apply GlobalTheory.GLm.ParBasic.par_basic <;> assumption)
