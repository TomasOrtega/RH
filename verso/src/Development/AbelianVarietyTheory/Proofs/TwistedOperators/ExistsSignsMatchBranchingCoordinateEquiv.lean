import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

namespace GlobalTheory.SepReal

private def optSumLeft (α β : Type) : Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

/- English proof (translation)
Establish `hF : Fintype.card {a // ¬ ε a = true} = Fintype.card {i // ¬ ε' i = true}`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Simplify `h` using `only [Bool.not_eq_true]`. Establish `hT : Fintype.card {a // ε a = true} = Fintype.card (Option {i // ε' i = true})`. Establish `h1` using `Fintype.card_subtype_compl (fun a => ε a = true)`.

Establish `h2` using `Fintype.card_subtype_compl (fun i => ε' i = true)`. Establish `h3` using `Fintype.card_subtype_le (fun a => ε a = true)`. Establish `h4` using `Fintype.card_subtype_le (fun i => ε' i = true)`. Simplify using `only [Fintype.card_fin] at h1 h2 h3 h4`. Rewrite using `[Fintype.card_option]`.

Use linear arithmetic over natural numbers and integers. Set `eT` to `Fintype.equivOfCardEq hT`. Set `eF` to `Fintype.equivOfCardEq hF`. Set `e : Option (Fin n) ≃ Fin (n + 1)` to `((Equiv.optionCongr (Equiv.sumCompl fun i => ε' i = true).symm).trans (optSumLeft _ _)).trans ((Equiv.sumCongr eT.symm eF.symm).trans (Equiv.sumCompl fun a => ε a = true))`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations.

Use `show ε ((eT.symm none : {a // ε a = true}) : Fin (n + 1)) = true`. Conclude with `(eT.symm none).2`. Introduce `i`. Distinguish the cases in `hi : ε' i = true`. Establish `: e (some i) = ((eT.symm (some ⟨i, hi⟩) : {a // ε a = true}) : Fin (n + 1))`.

Simplify using `[e, Equiv.sumCompl, hi, optSumLeft]`. Rewrite using `[this, (eT.symm (some ⟨i, hi⟩)).2, hi]`. Establish `: e (some i) = ((eF.symm ⟨i, hi⟩ : {a // ¬ ε a = true}) : Fin (n + 1))`. Simplify using `[e, Equiv.sumCompl, hi, optSumLeft]`. Rewrite using `[this]`.

Use `(eF.symm ⟨i, hi⟩).2` as an intermediate fact. Simplify using `only [Bool.not_eq_true] at this hi`. Rewrite using `[this, hi]`.
-/
theorem exists_signs_equiv {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card) :
    ∃ e : Option (Fin n) ≃ Fin (n + 1), Signs e ε ε' := by
  classical
  have hF : Fintype.card {a // ¬ ε a = true} = Fintype.card {i // ¬ ε' i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Bool.not_eq_true] using h
  have hT : Fintype.card {a // ε a = true} = Fintype.card (Option {i // ε' i = true}) := by
    have h1 := Fintype.card_subtype_compl (fun a => ε a = true)
    have h2 := Fintype.card_subtype_compl (fun i => ε' i = true)
    have h3 := Fintype.card_subtype_le (fun a => ε a = true)
    have h4 := Fintype.card_subtype_le (fun i => ε' i = true)
    simp only [Fintype.card_fin] at h1 h2 h3 h4
    rw [Fintype.card_option]
    omega
  let eT := Fintype.equivOfCardEq hT
  let eF := Fintype.equivOfCardEq hF
  let e : Option (Fin n) ≃ Fin (n + 1) :=
    ((Equiv.optionCongr (Equiv.sumCompl fun i => ε' i = true).symm).trans
      (optSumLeft _ _)).trans ((Equiv.sumCongr eT.symm eF.symm).trans (Equiv.sumCompl fun a => ε a = true))
  refine ⟨e, ?_, ?_⟩
  · show ε ((eT.symm none : {a // ε a = true}) : Fin (n + 1)) = true
    exact (eT.symm none).2
  · intro i
    by_cases hi : ε' i = true
    · have : e (some i) = ((eT.symm (some ⟨i, hi⟩) : {a // ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this, (eT.symm (some ⟨i, hi⟩)).2, hi]
    · have : e (some i) = ((eF.symm ⟨i, hi⟩ : {a // ¬ ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this]
      have := (eF.symm ⟨i, hi⟩).2
      simp only [Bool.not_eq_true] at this hi
      rw [this, hi]

end GlobalTheory.SepReal
