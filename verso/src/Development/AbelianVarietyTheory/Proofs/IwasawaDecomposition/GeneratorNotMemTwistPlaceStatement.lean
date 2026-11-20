import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.PdNotType.pD_not_type` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGeneratorNotMemTwistPlace.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.generator_not_mem_twist_place : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  first | exact @GlobalTheory.Mem.PdNotType.pD_not_type | exact GlobalTheory.Mem.PdNotType.pD_not_type | (intros; apply GlobalTheory.Mem.PdNotType.pD_not_type <;> assumption)
