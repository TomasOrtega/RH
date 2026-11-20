import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselLieTriangularVanishing
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BesselNilp.bessel_dC` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBesselLieTriangularVanishing.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v := by
  first | exact @GlobalTheory.BesselNilp.bessel_dC | exact GlobalTheory.BesselNilp.bessel_dC | (intros; apply GlobalTheory.BesselNilp.bessel_dC <;> assumption)
