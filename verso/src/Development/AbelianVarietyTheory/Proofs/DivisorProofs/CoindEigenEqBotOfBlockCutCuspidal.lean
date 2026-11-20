import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.MackeyCut

/- English proof (translation)
Introduce `F _ ψ r V _ _ b σ hσ j w x hx a c haj hjc hb`. Take `⟨_, _, _, hcusp⟩` from `hσ`. Establish `hy' : ∀ y ∈ eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))), ∀ p : blockTri (κ` using `F) b, x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r → σ p y = ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x)) • y := by`. Introduce `y hy p hp`. Unfold `eig at hy`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hy`. Establish `h` using `hy p hp`. Simplify `h` using `[sub_eq_zero]`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

Rewrite using `[Submodule.mem_bot]`. Set `S : Finset (Fin r)` to `Finset.univ.filter (fun i => (w.symm i).val < j)`. Use `hcusp S ⟨w a, w c, hb, ?_, ?_⟩ y ?_` and prove the remaining obligations. Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]`. Conclude with `haj`.

Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt]`. Conclude with `hjc`. Introduce `u hu`. Establish `hent : ∀ a' c' : Fin r, (c'.val ≤ a'.val ∨ (c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j)) → ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a') (w c') = (1 : Matrix (Fin r) (Fin r) F) (w a') (w c')`. Introduce `a' c' h`.

Assume the negation of the conclusion as `hne`. Take `⟨_, h1, h2⟩` from `hu _ _ hne`. Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt] at h1 h2`. Use linear arithmetic over natural numbers and integers. Establish `hU : x⁻¹ * (u : GL (Fin r) F) * x ∈ unip F r` using `by show x⁻¹ * (u : GL (Fin r) F) * x ∈ blockTri (κ := F) (fun a : Fin r => a.val) ∧ ∀ i, ((x⁻¹ * (u : GL (Fin r) F) * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i i = 1`.

Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_blockTri]`. Introduce `a' c' h`. Establish `h' : c'.val < a'.val` using `h`. Rewrite using `[hx, hent a' c' (Or.inl h'.le)]`.

Use `Matrix.one_apply_ne ?_` and prove the remaining obligations. Introduce `e`. Use `w.injective e` as an intermediate fact. Rewrite `h'` using `[this]`. Conclude with `lt_irrefl _ h'`.

Rewrite using `[hx, hent i i (Or.inl le_rfl), Matrix.one_apply_eq]`. Establish `hE : edgeSum (cutEdge j) (x⁻¹ * (u : GL (Fin r) F) * x) = 0`. Unfold `edgeSum`. Use `Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun c' _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Establish `h' : c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j`. Unfold `cutEdge at h`. Conclude with `h`. Rewrite using `[hx, hent a' c' (Or.inr h')]`. Use `Matrix.one_apply_ne ?_` and prove the remaining obligations.

Introduce `e`. Use `w.injective e` as an intermediate fact. Rewrite `h'` using `[this]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Rewrite using `[hy' y hy u hU, hE, AddChar.map_zero_eq_one, one_smul]`.
-/
theorem eig_eq_bot_of_cut : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) = b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  intro F _ ψ r V _ _ b σ hσ j w x hx a c haj hjc hb
  obtain ⟨_, _, _, hcusp⟩ := hσ

  have hy' : ∀ y ∈ eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r}
      (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))),
      ∀ p : blockTri (κ := F) b, x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r →
        σ p y = ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x)) • y := by
    intro y hy p hp
    unfold eig at hy
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hy
    have h := hy p hp
    simpa [sub_eq_zero] using h
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]

  let S : Finset (Fin r) := Finset.univ.filter (fun i => (w.symm i).val < j)
  refine hcusp S ⟨w a, w c, hb, ?_, ?_⟩ y ?_
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact haj
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt]
    exact hjc
  · intro u hu

    have hent : ∀ a' c' : Fin r, (c'.val ≤ a'.val ∨ (c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j)) →
        ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a') (w c') = (1 : Matrix (Fin r) (Fin r) F) (w a') (w c') := by
      intro a' c' h
      by_contra hne
      obtain ⟨_, h1, h2⟩ := hu _ _ hne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, not_lt] at h1 h2
      omega
    have hU : x⁻¹ * (u : GL (Fin r) F) * x ∈ unip F r := by
      show x⁻¹ * (u : GL (Fin r) F) * x ∈ blockTri (κ := F) (fun a : Fin r => a.val) ∧
        ∀ i, ((x⁻¹ * (u : GL (Fin r) F) * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i i = 1
      refine ⟨?_, fun i => ?_⟩
      · rw [mem_blockTri]
        intro a' c' h
        have h' : c'.val < a'.val := h
        rw [hx, hent a' c' (Or.inl h'.le)]
        refine Matrix.one_apply_ne ?_
        intro e
        have := w.injective e
        rw [this] at h'
        exact lt_irrefl _ h'
      · rw [hx, hent i i (Or.inl le_rfl), Matrix.one_apply_eq]
    have hE : edgeSum (cutEdge j) (x⁻¹ * (u : GL (Fin r) F) * x) = 0 := by
      unfold edgeSum
      refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun c' _ => ?_
      split_ifs with h
      · have h' : c'.val = a'.val + 1 ∧ a'.val + 1 ≠ j := by
          unfold cutEdge at h
          exact h
        rw [hx, hent a' c' (Or.inr h')]
        refine Matrix.one_apply_ne ?_
        intro e
        have := w.injective e
        rw [this] at h'
        omega
      · rfl
    rw [hy' y hy u hU, hE, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.FinGL.MackeyCut
