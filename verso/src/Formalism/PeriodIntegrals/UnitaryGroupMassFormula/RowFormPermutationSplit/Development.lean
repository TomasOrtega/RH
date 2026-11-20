import Formalism.PeriodIntegrals.QmRowForm

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmRowForm

def doubleRowFormSum {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (x : Fin t → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t), ∑ τ : Equiv.Perm (Fin t),
    (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm E (x k) (a (σ k)) (b (τ k))).prod

def DblDec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ),
      doubleRowFormSum E a b (fun k : Fin t => u - (k : ℂ)) = (t.factorial : ℂ) • qminor E a b u

def DblInc : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ),
      doubleRowFormSum E a b (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) =
        (t.factorial : ℂ) • PI.qminorRow E a b u

def DblPerm : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (x : Fin t → ℂ) (π : Equiv.Perm (Fin t)),
      doubleRowFormSum E a b (x ∘ π) = doubleRowFormSum E a b x

/- English proof (translation)
Introduce `A _ _ n t E hE a b u`. Establish `hx : (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) ∘ (Fin.revPerm : Equiv.Perm (Fin t)) = fun k : Fin t => u - (k : ℂ)`. Use function extensionality and compare the values at `k`. Establish `hk : (k : ℕ) + 1 ≤ t` using `k.isLt`. Simplify using `only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hk, Nat.cast_add, Nat.cast_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `h1 A n t E hE a b u`. Establish `e2` using `h2 A n t E hE a b u`. Establish `e3` using `h3 A n t E hE a b (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) Fin.revPerm`. Rewrite `e3` using `[hx, e1, e2]`.

Establish `hf : (t.factorial : ℂ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero t`. Establish `e4` using `congrArg (fun y : A => ((t.factorial : ℂ)⁻¹) • y) e3`. Simplify using `only [smul_smul, inv_mul_cancel₀ hf, one_smul] at e4`. Conclude with `e4`.
-/
theorem rowForm_of (h1 : DblDec) (h2 : DblInc) (h3 : DblPerm) : PI.RowForm := by
  intro A _ _ n t E hE a b u
  have hx : (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) ∘ (Fin.revPerm : Equiv.Perm (Fin t)) =
      fun k : Fin t => u - (k : ℂ) := by
    funext k
    have hk : (k : ℕ) + 1 ≤ t := k.isLt
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hk, Nat.cast_add,
      Nat.cast_one]
    ring
  have e1 := h1 A n t E hE a b u
  have e2 := h2 A n t E hE a b u
  have e3 := h3 A n t E hE a b (fun k : Fin t => u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) Fin.revPerm
  rw [hx, e1, e2] at e3
  have hf : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have e4 := congrArg (fun y : A => ((t.factorial : ℂ)⁻¹) • y) e3
  simp only [smul_smul, inv_mul_cancel₀ hf, one_smul] at e4
  exact e4

/- English proof (translation)
Unfold `PI.QmRowForm`. Conclude with `rowForm_of h1 h2 h3`.
-/
theorem qmRowForm_of (h1 : DblDec) (h2 : DblInc) (h3 : DblPerm) : PI.QmRowForm := by
  unfold PI.QmRowForm
  exact rowForm_of h1 h2 h3

end PI.UnitaryGroupMassFormula.QmRowForm
