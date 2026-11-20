import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTop
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGoodEigSumSupComplEigSumEqTop.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i → D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  first | exact @GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | exact GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | (intros; apply GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top <;> assumption)
