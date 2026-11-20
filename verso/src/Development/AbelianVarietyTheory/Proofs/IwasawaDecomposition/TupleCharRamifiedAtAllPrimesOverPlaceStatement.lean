import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTupleCharRamifiedAtAllPrimesOverPlace.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  first | exact @GlobalTheory.Mem.HD.RamBoth.ram_both | exact GlobalTheory.Mem.HD.RamBoth.ram_both | (intros; apply GlobalTheory.Mem.HD.RamBoth.ram_both <;> assumption)
