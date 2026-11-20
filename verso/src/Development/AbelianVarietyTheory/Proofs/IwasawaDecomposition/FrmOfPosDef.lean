import Mathlib
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]

open Classical in

def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

/- English proof (translation)
Unfold `frm`. Use `split_ifs with h`. Conclude with `(frameOfSpec _ _ h).1`. Simplify using the standard rewrite rules.
-/
theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

/- English proof (translation)
Unfold `frm`. Rewrite using `[if_pos h]`.
-/
theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [if_pos h]

end Frames

section Coord

variable {K : Type} [Field K]

def rdx {a b : ℕ} (h : a = b) : (Fin b → K) ≃ₗ[K] (Fin a → K) := LinearEquiv.funCongrLeft K K (finCongr h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdx_apply {a b : ℕ} (h : a = b) (x : Fin b → K) (i : Fin a) : rdx h x i = x (Fin.cast h i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[rdx_apply]`. Both sides reduce to the same expression.
-/
theorem rdx_refl {a : ℕ} (h : a = a) (x : Fin a → K) : rdx h x = x := by
  funext i
  rw [rdx_apply]
  rfl

end Coord

end GlobalTheory.AmbCrd

end
