import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSelfDualStableLatticeUnitOrbitsFinite.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | exact GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | (intros; apply GlobalTheory.UnitLemma.OrbitFinite.orbits_finite <;> assumption)
