import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

/- English proof (translation)
Use `⟨0, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0`. Establish `hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Establish `hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT)`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises.

Unfold `MA.wq`. Conclude with `mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _) (pow_pos (sub_pos.2 hy.2) _)`. Establish `hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0`. Introduce `π`. Establish `hsm` using `En.trace_smoothness E Wp Wq S T v hplace e he X hX π`.

Establish `h` using `h0 π`. Unfold `trJ at h`. Rewrite `h` using `[En.toSm_val_of_mem _ hsm]`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd h (Complex.ofReal_ne_zero.2 hw.ne')`.

Conclude with `h`. Establish `hfib` using `En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy`. Rewrite using `[(he.2 y.2 hy.2).2.2 _ hfib]`. Simplify using `[hin]`.
-/
theorem self_adjoint_zero_holds : SAZero := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT) := by
    apply Real.sqrt_pos.2
    unfold MA.wq
    exact mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _)
      (pow_pos (sub_pos.2 hy.2) _)
  have hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0 := by
    intro π
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he X hX π
    have h := h0 π
    unfold trJ at h
    rw [En.toSm_val_of_mem _ hsm] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (Complex.ofReal_ne_zero.2 hw.ne')
    · exact h
  have hfib := En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy
  rw [(he.2 y.2 hy.2).2.2 _ hfib]
  simp [hin]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
