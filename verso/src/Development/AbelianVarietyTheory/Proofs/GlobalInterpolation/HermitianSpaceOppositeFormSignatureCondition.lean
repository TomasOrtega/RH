import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.NegSpace

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Set `s` to `Equiv.sumComm (Fin p) (Fin q)`. Use `⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩` and prove the remaining obligations. Establish `e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]`. Rewrite using `[e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]`. Both sides reduce to the same expression.
-/
theorem hasSignature_neg_swap {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩
  have e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]
  rw [e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]
  rfl

/- English proof (translation)
Introduce `E _ _ _ W h τ`. Establish `e : (neg W).gram.map τ = -W.gram.map τ` using `Matrix.ext fun i j => map_neg τ (W.gram i j)`. Rewrite using `[e]`. Conclude with `hasSignature_neg_swap (h τ)`.
-/
theorem sigOK_neg : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  intro E _ _ _ W h τ
  have e : (neg W).gram.map τ = -W.gram.map τ := Matrix.ext fun i j => map_neg τ (W.gram i j)
  rw [e]
  exact hasSignature_neg_swap (h τ)

end GlobalTheory.NegSpace
