import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimePlacesIsSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypePrimeSplit.typePrime_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTypePrimePlacesIsSplitPlace.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.typePrime_places_isSplitPlace : ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v := by
  first | exact @GlobalTheory.TypePrimeSplit.typePrime_split | exact GlobalTheory.TypePrimeSplit.typePrime_split | (intros; apply GlobalTheory.TypePrimeSplit.typePrime_split <;> assumption)
