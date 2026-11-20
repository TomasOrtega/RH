import Mathlib

open Equiv

/- English proof (translation)
Introduce `α n F h1 h2`. Set `S : Subgroup (Equiv.Perm (Fin (n+2)))` to `{ carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L} mul_mem' := by`. Introduce `σ τ hσ hτ`. Establish `hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L` using `hσ`. Establish `hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L` using `hτ`.

Use `show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L`. Introduce `L`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `one_mem' := by show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L`. Introduce `L`.

Both sides reduce to the same expression. Use the proof step `inv_mem' := by`. Introduce `σ hσ`. Establish `hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L` using `hσ`. Use `show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L`.

Introduce `L`. Combine the equalities or inequalities in the displayed calculation. Establish `memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L` using `fun σ => Iff.rfl`. Establish `hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S`. Introduce `e`.

Rewrite using `[memS]`. Introduce `L`. Establish `hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i))`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `[Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]`. Rewrite using `[hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]`. Establish `hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S`. Rewrite using `[memS]`.

Introduce `L`. Establish `e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Both sides reduce to the same expression.

Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Both sides reduce to the same expression. Both sides reduce to the same expression. Establish `e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α)`. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `a1 : (k.succ.succ : Fin (n+2)) ≠ 0` using `Fin.succ_ne_zero _`.

Establish `a2 : (k.succ.succ : Fin (n+2)) ≠ 1`. Introduce `h`. Rewrite `h` using `[← Fin.succ_zero_eq_one]`. Conclude with `Fin.succ_ne_zero _ (Fin.succ_injective _ h)`. Simplify using `[Equiv.swap_apply_of_ne_of_ne a1 a2]`.

Rewrite using `[e2, ← h2 (L 0) (L 1)]`. Conclude with `congrArg F e1.symm`. Establish `hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S`. Introduce `p`. Use `Fin.cases ?_ (fun k => ?_) p` and prove the remaining obligations.

Rewrite using `[Equiv.swap_self]`. Conclude with `S.one_mem`. Establish `h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0` using `by simp`. Establish `h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ`. Rewrite using `[← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]`.

Simplify using the standard rewrite rules. Establish `hc` using `Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1`. Rewrite `hc` using `[h0, h1']`. Rewrite using `[hc]`. Conclude with `S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))`.

Establish `hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))), Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e)`. Introduce `p e`. Use extensionality with `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `[Equiv.Perm.decomposeFin_symm_apply_succ]`. Introduce `L e`. Establish `he : e ∈ S`. Rewrite using `[← Equiv.Perm.decomposeFin.symm_apply_apply e]`. Break down `Equiv.Perm.decomposeFin e with ⟨p, e'⟩` into its components or cases.

Rewrite using `[hdec]`. Conclude with `S.mul_mem (hp p) (hfix e')`. Conclude with `(memS e).1 he L`.
-/
theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
