import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedFiniteNormAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovHt.Link.nrmFin_one_bdQ_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundedFiniteNormAlmostAll.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.bounded_finite_norm_almost_all : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (k : s.Comp), ∃ c : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (Function.support c).Finite ∧ ∀ v e y, (bdQ P k).nrmFin v 1 1 e y ≤ Real.exp (c v) := by
  first | exact @GlobalTheory.CovHt.Link.nrmFin_one_bdQ_le | exact GlobalTheory.CovHt.Link.nrmFin_one_bdQ_le | (intros; apply GlobalTheory.CovHt.Link.nrmFin_one_bdQ_le <;> assumption)
