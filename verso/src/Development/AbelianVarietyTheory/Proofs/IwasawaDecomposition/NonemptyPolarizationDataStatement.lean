import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyPolarizationData
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNonemptyPolarizationData.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.nonempty_polarization_data : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ), Nonempty (PolDat s Φ hm h0) := by
  first | exact @GlobalTheory.existsPolDat | exact GlobalTheory.existsPolDat | (intros; apply GlobalTheory.existsPolDat <;> assumption)
