import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModpFramesPullback.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.modp_frames_pullback : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (p : ℕ)
    (ι : Type) (N : ℕ) (U : ι → X.Opens) (M : ι → Matrix (Fin N) (Fin N) X.functionField) (c : ι → Fin N → X.functionFieldˣ),
    GlobalTheory.FrameGlue.ModPFrames p U M c →
    GlobalTheory.FrameGlue.ModPFrames p (fun a => π ⁻¹ᵁ U a) (fun a => (M a).map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ))
      (fun a i => Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c a i)) := by
  first | exact @GlobalTheory.FrameGlue.modPFrames_pull | exact GlobalTheory.FrameGlue.modPFrames_pull | (intros; apply GlobalTheory.FrameGlue.modPFrames_pull <;> assumption)
