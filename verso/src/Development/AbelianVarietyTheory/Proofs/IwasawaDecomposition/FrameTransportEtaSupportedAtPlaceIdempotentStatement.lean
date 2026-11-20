import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.R3.LiftBrg.eta_suppAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFrameTransportEtaSupportedAtPlaceIdempotent.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | exact GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_suppAt <;> assumption)
