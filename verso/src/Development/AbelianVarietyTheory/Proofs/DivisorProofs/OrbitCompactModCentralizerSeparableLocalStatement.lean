import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOrbitCompactModCentralizerSeparableLocal.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.orbit_compact_mod_centralizer_separable_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  first | exact @GlobalTheory.OrbitCptW.orbit_cpt_w | exact GlobalTheory.OrbitCptW.orbit_cpt_w | (intros; apply GlobalTheory.OrbitCptW.orbit_cpt_w <;> assumption)
