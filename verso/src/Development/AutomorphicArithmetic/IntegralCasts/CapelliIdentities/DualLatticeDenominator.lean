import Mathlib

/- English proof (translation)
Introduce `A _ _ F V _ _ _ _ _ _ _ Y hY z`. Establish `hz : z ∈ Submodule.span F (Y : Set V)`. Rewrite using `[hY.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`.

Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Y.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Y.smul_mem b hax`.

Rewrite using `[mul_smul]`. Conclude with `Y.smul_mem a hby`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨⟨d, hd⟩, n, hn⟩` from `IsLocalization.exists_integer_multiple (nonZeroDivisors A) c`.

Use `⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩` and prove the remaining obligations. Establish `h : (a * d) • c • x = n • a • x`. Rewrite using `[mul_smul, ← smul_assoc d c x]`. Establish `h2 : d • c = algebraMap A F n` using `hn.symm`. Rewrite using `[h2, algebraMap_smul, smul_comm]`.

Rewrite using `[h]`. Conclude with `Y.smul_mem n hax`.
-/
theorem UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by
  intro A _ _ F V _ _ _ _ _ _ _ Y hY z
  have hz : z ∈ Submodule.span F (Y : Set V) := by
    rw [hY.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨d, hd⟩, n, hn⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors A) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩
    have h : (a * d) • c • x = n • a • x := by
      rw [mul_smul, ← smul_assoc d c x]
      have h2 : d • c = algebraMap A F n := hn.symm
      rw [h2, algebraMap_smul, smul_comm]
    rw [h]
    exact Y.smul_mem n hax
