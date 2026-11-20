import Mathlib

/- English proof (translation)
Introduce `k K G ι _ _ _ _ φ f h`. Establish `key : ∀ M : Matrix ι ι k, M ∈ Submodule.span k (Set.range f) → M.map (⇑φ : k → K) ∈ Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K))`. Introduce `M hM`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g, rfl⟩`. Consider the case `zero`. Establish `e : (0 : Matrix ι ι k).map (⇑φ : k → K) = 0`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `e : (x + y).map (⇑φ : k → K) = x.map (⇑φ : k → K) + y.map (⇑φ : k → K)`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Establish `e : (a • x).map (⇑φ : k → K) = φ a • x.map (⇑φ : k → K)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hx`.

Rewrite using `[eq_top_iff]`. Introduce `N _`. Rewrite using `[Matrix.matrix_eq_sum_single N]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `e : Matrix.single i j (N i j) = N i j • (Matrix.single i j (1 : k)).map (⇑φ : k → K)`.

Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : i = a ∧ j = b <;> simp [Matrix.single, hab]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (key _ (h ▸ Submodule.mem_top))`.
-/
theorem UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top :
    ∀ {k K G ι : Type} [inst : Field k] [inst_1 : Field K]
    [Fintype ι] [DecidableEq ι] (φ : k →+* K) (f : G → Matrix ι ι k),
    Submodule.span k (Set.range f) = ⊤ → Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) = ⊤ := by
  intro k K G ι _ _ _ _ φ f h
  have key : ∀ M : Matrix ι ι k, M ∈ Submodule.span k (Set.range f) →
      M.map (⇑φ : k → K) ∈
        Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero =>
      have e : (0 : Matrix ι ι k).map (⇑φ : k → K) = 0 := by
        ext i j
        simp
      rw [e]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have e : (x + y).map (⇑φ : k → K) = x.map (⇑φ : k → K) + y.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : (a • x).map (⇑φ : k → K) = φ a • x.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro N _
  rw [Matrix.matrix_eq_sum_single N]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (N i j)
      = N i j • (Matrix.single i j (1 : k)).map (⇑φ : k → K) := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [Matrix.single, hab]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ (h ▸ Submodule.mem_top))
