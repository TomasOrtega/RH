import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FConjugateTypeVector.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.conjugate_type_vector : ∀ (D : D7) (Rw : GlobalTheory.HeightCounting.RowSide D) (L : ∀ k, LabelDatum (D.host.g k)) (rc : GlobalTheory.SerSys.Corr D) (cp : GlobalTheory.GoodTypes.Comp D), LabTie D L → LabParam D L rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.GoodTypes.SeriesConj D → (∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (σ : D.what₂.FT), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) → ∀ x : V, x ≠ 0 → (∀ a, ρ.asAlgebraHom a x ∈ W) → ρ.asAlgebraHom D.ntypes.e0 x = x → D.nd.goodRow σ := by
  first | exact @GlobalTheory.GoodFree.good_of_vector_row | exact GlobalTheory.GoodFree.good_of_vector_row | (intros; apply GlobalTheory.GoodFree.good_of_vector_row <;> assumption)
