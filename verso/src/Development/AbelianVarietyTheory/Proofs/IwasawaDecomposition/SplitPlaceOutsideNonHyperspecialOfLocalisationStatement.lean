import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOutsideNonHyperspecialOfLocalisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitOutPlace.not_mem_gPl_qPl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSplitPlaceOutsideNonHyperspecialOfLocalisation.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := by
  first | exact @GlobalTheory.SplitOutPlace.not_mem_gPl_qPl | exact GlobalTheory.SplitOutPlace.not_mem_gPl_qPl | (intros; apply GlobalTheory.SplitOutPlace.not_mem_gPl_qPl <;> assumption)
