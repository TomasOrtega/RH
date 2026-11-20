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
Introduce `k _ Ω _ _ N x e Nb r h hZ hV`. Take `⟨-, P, -, hP, hPn⟩` from `hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩`. Take `⟨-, Q, -, hQ, hQn⟩` from `hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV) isVeryAmple_twistSys_one`. Take `⟨n₀, hn₀⟩` from `eventually_atTop.mp (hPn.and hQn)`. Establish `hPQ : P = Q`.

Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `: a + n₀ = b + n₀` using `by simpa using hab`. Use linear arithmetic over natural numbers and integers.

Introduce `m`. Take `⟨h1, h2⟩` from `hn₀ (m + n₀) (Nat.le_add_left n₀ m)`. Express the relevant statement in the definitionally equal form `P.eval _ = Q.eval _`. Rewrite using `[← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]`. Both sides reduce to the same expression.

Establish `hnum : (interNum (primeOf (S` using `k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) = (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by`. Rewrite using `[← hP, hPQ, hQ]`. Both sides reduce to the same expression. Conclude with `hnum` after adjusting the coercions.
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
