import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

/- English proof (translation)
Establish `key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0`. Introduce `M hM`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`.

Conclude with `h g`. Consider the case `zero => simp [bar]`. Consider the case `add x y _ _ hx hy`. Establish `e : bar X (x + y) = bar X x + bar X y`. Use extensionality with `i j`.

Simplify using `[bar]`. Rewrite using `[e, add_mul, Matrix.trace_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx`. Establish `e : bar X (a • x) = a • bar X x`. Use extensionality with `i j`.

Simplify using `only [bar]`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, Algebra.smul_def]`. Rewrite using `[e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]`. Use extensionality with `i j`. Establish `t` using `key _ (hs (Matrix.single j i 1))`.

Establish `e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀)`. Use extensionality with `a b`. Simplify using `[bar, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `t` using `[e]`.

Simplify `t` using `[Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Algebra.smul_def]`.
-/
private theorem k0 {O G : Type} [CommRing O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O)
    (hs : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) (X : Type) [CommRing X] [Algebra O X]
    (W : Matrix (Fin n) (Fin n) X) (h : ∀ g, (bar X (ρ g) * W).trace = 0) : c₀ • W = 0 := by
  have key : ∀ M ∈ Submodule.span O (Set.range ρ), (bar X M * W).trace = 0 := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => simp [bar]
    | add x y _ _ hx hy =>
      have e : bar X (x + y) = bar X x + bar X y := by
        ext i j
        simp [bar]
      rw [e, add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx =>
      have e : bar X (a • x) = a • bar X x := by
        ext i j
        simp only [bar]
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
          Algebra.smul_def]
      rw [e, Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  have t := key _ (hs (Matrix.single j i 1))
  have e : bar X (c₀ • Matrix.single j i (1 : O)) = Matrix.single j i (algebraMap O X c₀) := by
    ext a b
    simp [bar, Matrix.single_apply]
    split_ifs <;> simp
  rw [e] at t
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Algebra.smul_def] using t

/- English proof (translation)
Introduce `O G _ _ _ n ρ c₀ hc hs`. Use `⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩` and prove the remaining obligations. Establish `hb : ∀ g, (bar O (ρ g) * W).trace = 0`. Introduce `g`. Establish `e : bar O (ρ g) = ρ g`.

Use extensionality with `i j`. Simplify using `[bar]`. Rewrite using `[e]`. Conclude with `hW g`. Use `k0 ρ c₀ hs O W hb` as an intermediate fact.

Use extensionality with `i j`. Use `congrFun (congrFun this i) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this`. Conclude with `(mul_eq_zero.mp this).resolve_left hc`.
-/
theorem UpperTheory.V.Th.Coc.kill0 :
    ∀ {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ W : Matrix (Fin n) (Fin n) O, (∀ g, (ρ g * W).trace = 0) → W = 0) ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (W : Matrix (Fin n) (Fin n) X), (∀ g, (bar X (ρ g) * W).trace = 0) → c₀ • W = 0 := by
  intro O G _ _ _ n ρ c₀ hc hs
  refine ⟨fun W hW => ?_, fun X _ _ W hW => k0 ρ c₀ hs X W hW⟩
  have hb : ∀ g, (bar O (ρ g) * W).trace = 0 := by
    intro g
    have e : bar O (ρ g) = ρ g := by
      ext i j
      simp [bar]
    rw [e]
    exact hW g
  have := k0 ρ c₀ hs O W hb
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hc
