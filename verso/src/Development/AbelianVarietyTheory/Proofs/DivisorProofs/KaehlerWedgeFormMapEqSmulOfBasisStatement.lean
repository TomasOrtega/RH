import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKaehlerWedgeFormMapEqSmulOfBasis.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  first | exact @GlobalTheory.TopFormAppend.dForm_append_eq_smul | exact GlobalTheory.TopFormAppend.dForm_append_eq_smul | (intros; apply GlobalTheory.TopFormAppend.dForm_append_eq_smul <;> assumption)
