import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatInd.DCoset.finite_dcoset` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUnitaryDoubleCosetFiniteLeftCosets.lean&line=197#L197)
-/
theorem _root_.GlobalTheory.T.unitary_doubleCoset_finite_left_cosets : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (ϖ : K) (σ : K →+* K) (q n : ℕ), IsUnramInv ϖ σ q → ∀ s : GU σ n, Set.Finite {c : GU σ n ⧸ KU σ n | ∃ a ∈ KU σ n, ((a * s : GU σ n) : GU σ n ⧸ KU σ n) = c} := by
  first | exact @GlobalTheory.SatInd.DCoset.finite_dcoset | exact GlobalTheory.SatInd.DCoset.finite_dcoset | (intros; apply GlobalTheory.SatInd.DCoset.finite_dcoset <;> assumption)
