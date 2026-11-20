import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCoeffDetGenericSumMemHeckeAlgebra.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | exact GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | (intros; apply GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing <;> assumption)
