import Formalism.RealPlaceAnalysis.StatementA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirCommutation

open scoped TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd`.
-/
theorem casComm_casK_comm {A : Type} [Ring A] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) (hcd : ε c = ε d) :
    CasK ε E * E c d = E c d * CasK ε E :=
  _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd

/- English proof (translation)
Introduce `A _ n ε E hE`. Use `⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩` and prove the remaining obligations. Establish `h` using `casComm_casK_comm (fun _ => true) E hE c d rfl`. Establish `hC : CasK (fun _ : Fin n => true) E = Cas E` using `by simp [CasK, Cas]`. Rewrite `h` using `[hC]`. Then use the resulting hypothesis.
-/
theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩
  have h := casComm_casK_comm (fun _ => true) E hE c d rfl
  have hC : CasK (fun _ : Fin n => true) E = Cas E := by simp [CasK, Cas]
  rwa [hC] at h

end Formalism.REAL
