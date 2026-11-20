import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoe
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsComplexEmbeddingReadingFractionRingOverCoe.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  first | exact @GlobalTheory.ReadingEmb.exists_complex_emb | exact GlobalTheory.ReadingEmb.exists_complex_emb | (intros; apply GlobalTheory.ReadingEmb.exists_complex_emb <;> assumption)
