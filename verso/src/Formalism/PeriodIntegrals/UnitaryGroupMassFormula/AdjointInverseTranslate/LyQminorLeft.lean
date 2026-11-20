import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAaVector

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [EabH, RdV, Matrix.mul_assoc]`.
-/
theorem ly_Eab_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun x => F (s * x)) = fun x => EabH H a b F (s * x) := by
  funext x
  simp only [EabH, RdV, Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Formalism.QuantumDeterminants.Top, EabH, RdV, Matrix.mul_assoc]`.
-/
theorem ly_Top_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Top (EabH H) v a b (fun x => F (s * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) v a b F (s * x) := by
  funext x
  simp only [Formalism.QuantumDeterminants.Top, EabH, RdV, Matrix.mul_assoc]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons T l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih (fun T' hT' => hl T' (by simp [hT'])), hl T (by simp)]`.
-/
theorem ly_foldr_comm {X E : Type*} (L : (X → E) → (X → E)) (l : List ((X → E) → (X → E)))
    (hl : ∀ T ∈ l, ∀ f, T (L f) = L (T f)) (f : X → E) :
    l.foldr (fun T h => T h) (L f) = L (l.foldr (fun T h => T h) f) := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hl T' (by simp [hT'])), hl T (by simp)]

/- English proof (translation)
Unfold `qminorOp`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.smul_apply]`. Use `congr 1`.

Rewrite using `[ly_foldr_comm (fun f y => f (s * y)) _ ?_ F]`. Introduce `T hT f`. Simplify using `only [List.mem_ofFn, Set.mem_range] at hT`. Take `⟨i, rfl⟩` from `hT`. Conclude with `ly_Top_left H _ _ _ f s`.
-/
theorem ly_qminor_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) a b u (fun y => F (s * y)) x = qminorOp (EabH H) a b u F (s * x) := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply]
  congr 1
  rw [ly_foldr_comm (fun f y => f (s * y)) _ ?_ F]
  intro T hT f
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨i, rfl⟩ := hT
  exact ly_Top_left H _ _ _ f s

/- English proof (translation)
Unfold `LeftAA`. Introduce `E _ _ k r z m hm u ell F s g hs hg`. Prove the components needed by the constructor for the conclusion. Simplify using `only [AAop]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations.

Rewrite using `[ly_qminor_left, coef_left_aa k r z m hm s g c hs]`. Simplify using `only [AAvop]`. Use `Finset.sum_congr rfl (fun B _ => ?_)` and prove the remaining obligations. Rewrite using `[ly_qminor_left, coef_left_aa_vector k r z m hm s g B hs hg]`.
-/
theorem left_aa : LeftAA := by
  unfold LeftAA
  intro E _ _ k r z m hm u ell F s g hs hg
  constructor
  · simp only [AAop]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [ly_qminor_left, coef_left_aa k r z m hm s g c hs]
  · simp only [AAvop]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [ly_qminor_left, coef_left_aa_vector k r z m hm s g B hs hg]

end AAInvW
