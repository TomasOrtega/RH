import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDimSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSecsSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleHilbertSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDegreeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem VeryAmpleDegree.proof (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum

end

end GroundTheory.Heights₂.Heights.Kleiman
