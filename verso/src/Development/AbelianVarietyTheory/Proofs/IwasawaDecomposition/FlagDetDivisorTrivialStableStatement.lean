import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDetDivisorTrivialStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagAmple.topDet_pull_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlagDetDivisorTrivialStable.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.flag_det_divisor_trivial_stable : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ τ : D.host.E →+* ℂ, GlobalTheory.CechPic.pull ((Φ.C k).π ⁻¹ᵁ V).ι (toPic (GlobalTheory.FlagAmple.detDiv (Φ.C k) τ (S.Dw.mult τ))) = 0 := by
  first | exact @GlobalTheory.FlagAmple.topDet_pull_eq_zero | exact GlobalTheory.FlagAmple.topDet_pull_eq_zero | (intros; apply GlobalTheory.FlagAmple.topDet_pull_eq_zero <;> assumption)
