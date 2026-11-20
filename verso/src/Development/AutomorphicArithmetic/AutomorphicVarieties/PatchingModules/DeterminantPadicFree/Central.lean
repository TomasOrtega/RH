import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `F G _ _ n D Z hZ`. Establish `key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X`. Introduce `X hX`. Rewrite `hX` using `[← D.span]`. Proceed by induction on `hX using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `hZ g hg`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]`.

Consider the case `smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]`. Use `⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩` and prove the remaining obligations. Use extensionality with `i j`. Distinguish the cases in `hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)`. Simplify using `using (hO i j).1 hij`.

Establish `hne : i ≠ j` using `fun h => hij (by rw [h])`. Establish `hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a`. Introduce `p q`. Use `⟨fun _ => Submodule.mem_top, fun h => ?_⟩` and prove the remaining obligations. Establish `hpq : p ≠ q` using `fun e => h (by rw [e])`.

Simplify using `[Matrix.diagonal_apply_ne _ hpq]`. Establish `h` using `congrFun (congrFun (key _ hE) i) j`. Rewrite `h` using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify `h` using `[Pi.single_eq_of_ne hne.symm]`.
-/
theorem UpperTheory.V.Pa.Det.central :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (Z : Matrix (Fin n) (Fin n) F), (∀ g ∈ D.G', D.r g * Z = Z * D.r g) → (Z ∈ Od F F n D.a → Z = 0) ∧ (Z ∈ Ev F F n D.a → ∀ g, D.r g * Z = Z * D.r g) := by
  intro F G _ _ n D Z hZ
  have key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact hZ g hg
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  refine ⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩
  ext i j
  by_cases hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)
  · simpa using (hO i j).1 hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    have hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a := by
      intro p q
      refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
      have hpq : p ≠ q := fun e => h (by rw [e])
      simp [Matrix.diagonal_apply_ne _ hpq]
    have h := congrFun (congrFun (key _ hE) i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simpa [Pi.single_eq_of_ne hne.symm] using h
