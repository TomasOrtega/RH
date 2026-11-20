import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentPullbackLatticeVectorMemDualSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AwayLat.prV_pullV_mem_latS_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPlaceComponentPullbackLatticeVectorMemDualSpan.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  first | exact @GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | exact GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | (intros; apply GlobalTheory.AwayLat.prV_pullV_mem_latS_dual <;> assumption)
