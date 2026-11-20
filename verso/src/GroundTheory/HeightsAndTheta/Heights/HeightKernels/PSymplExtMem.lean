import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplExtMem

/- English proof (translation)
Simplify using `[symplOmega]`.
-/
lemma omega_zero_left {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega (0 : l ⊕ l → R) w = 0 := by
  simp [symplOmega]

/- English proof (translation)
Simplify using `[symplOmega]`.
-/
lemma omega_zero_right {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega w (0 : l ⊕ l → R) = 0 := by
  simp [symplOmega]

variable {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma row_e : symplExt α β γ δ Q (Sum.inl 0) = symplCons α β 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma row_f : symplExt α β γ δ Q (Sum.inr 0) = symplCons γ δ 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma row_inl (i : Fin n) :
    symplExt α β γ δ Q (Sum.inl i.succ) = symplCons 0 0 (Q (Sum.inl i)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma row_inr (i : Fin n) :
    symplExt α β γ δ Q (Sum.inr i.succ) = symplCons 0 0 (Q (Sum.inr i)) := rfl

end PSymplExtMem

open PSymplExtMem in

/- English proof (translation)
Introduce `R _ n α β γ δ Q hdet hQ`. Rewrite using `[h1 R (Fin (n + 1))]`. Establish `hQ'` using `(h1 R (Fin n) Q).1 hQ`. Establish `hc` using `(h2 R n).2`. Apply the tactic sequence `rintro (x | x) (y | y) <;> cases x using Fin.cases <;> cases y using Fin.cases <;>`.

Apply the tactic sequence `simp only [row_e, row_f, row_inl, row_inr, hc, hQ', omega_zero_left, omega_zero_right] <;>`. Apply the tactic sequence `simp [Matrix.J, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj] <;>`. Use `first`. Consider the case `ring1`. Consider the case `linear_combination hdet`.

Consider the case `linear_combination (-1 : R) * hdet`. Consider the case `exact fun h => absurd (Eq.symm h) (Fin.succ_ne_zero _)`.
-/
theorem SymplExtMem.proof (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplExtMem.Statement := by
  intro R _ n α β γ δ Q hdet hQ
  rw [h1 R (Fin (n + 1))]
  have hQ' := (h1 R (Fin n) Q).1 hQ
  have hc := (h2 R n).2
  rintro (x | x) (y | y) <;> cases x using Fin.cases <;> cases y using Fin.cases <;>
    simp only [row_e, row_f, row_inl, row_inr, hc, hQ', omega_zero_left, omega_zero_right] <;>
    simp [Matrix.J, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj] <;>
    first
      | ring1
      | linear_combination hdet
      | linear_combination (-1 : R) * hdet
      | exact fun h => absurd (Eq.symm h) (Fin.succ_ne_zero _)

end GroundTheory.Heights₂.Heights
