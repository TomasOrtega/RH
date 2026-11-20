import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovHt.Link.ApproxSec.isCuspSec_of_mem_secs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMbarSectionsCuspidal.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.mbar_sections_cuspidal : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, IsCuspSec Φ k (τ • u) f := by
  first | exact @GlobalTheory.CovHt.Link.ApproxSec.isCuspSec_of_mem_secs | exact GlobalTheory.CovHt.Link.ApproxSec.isCuspSec_of_mem_secs | (intros; apply GlobalTheory.CovHt.Link.ApproxSec.isCuspSec_of_mem_secs <;> assumption)
