import Mathlib

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub r ⊤

/- English proof (translation)
Introduce `Γ k _ _ ρ hirr g`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨-, -, hmin⟩` from `hirr`. Set `L : Submodule k (Fin 2 → k)` to `LinearMap.ker ((LinearMap.proj (0 : Fin 2) : (Fin 2 → k) →ₗ[k] k) ∘ₗ Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) k))`.

Establish `hL : ∀ v, v ∈ L ↔ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) 0 = 0` using `fun v => Iff.rfl`. Establish `hg : ∀ w : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k).mulVec (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hinv : UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ L`.

Introduce `s v hv`. Rewrite `hv`, the goal using `[hL]`. Establish `key : (g : Matrix (Fin 2) (Fin 2) k).mulVec (((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v) = ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec ((g : Matrix (Fin 2) (Fin 2) k).mulVec v)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]`. Rewrite using `[key]`.

Generalize the expression as in `(g : Matrix (Fin 2) (Fin 2) k).mulVec v = w at hv`. Establish `h01` using `hcon s`. Generalize the expression as in `((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = M at h01`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, h01]`. Break down `hmin L le_top hinv with h | h` into its components or cases.

Establish `h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 1 1) ∈ L`. Rewrite using `[hL, hg]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h, Submodule.mem_bot]`. Establish `h2` using `hg (Pi.single 1 1)`.

Rewrite `h2` using `[h1, Matrix.mulVec_zero]`. Establish `h3` using `congrFun h2 1`. Simplify using `at h3`. Establish `h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) ∈ L`. Rewrite using `[h]`.

Conclude with `Submodule.mem_top`. Rewrite `h1` using `[hL, hg]`. Simplify using `at h1`.
-/
theorem UpperTheory.Reformulated.B.IrreducibleInvariant.exists_ne :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] (ρ : Γ →* GL (Fin (2 : ℕ)) k),
      UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr ρ →
        ∀ (g : GL (Fin (2 : ℕ)) k),
          ∃ (s : Γ),
            (↑(g * (ρ : Γ → GL (Fin (2 : ℕ)) k) s * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k) (0 : Fin (2 : ℕ))
                (1 : Fin (2 : ℕ)) ≠
              (0 : k) := by
  intro Γ k _ _ ρ hirr g
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hmin⟩ := hirr
  let L : Submodule k (Fin 2 → k) :=
    LinearMap.ker ((LinearMap.proj (0 : Fin 2) : (Fin 2 → k) →ₗ[k] k) ∘ₗ
      Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) k))
  have hL : ∀ v, v ∈ L ↔ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) 0 = 0 := fun v => Iff.rfl
  have hg : ∀ w : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k).mulVec
      (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ L := by
    intro s v hv
    rw [hL] at hv ⊢
    have key : (g : Matrix (Fin 2) (Fin 2) k).mulVec
        (((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec
          ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel_right]
    rw [key]
    generalize (g : Matrix (Fin 2) (Fin 2) k).mulVec v = w at hv
    have h01 := hcon s
    generalize ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = M at h01
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, h01]
  rcases hmin L le_top hinv with h | h
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 1 1) ∈ L := by
      rw [hL, hg]
      simp
    rw [h, Submodule.mem_bot] at h1
    have h2 := hg (Pi.single 1 1)
    rw [h1, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 1
    simp at h3
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) ∈ L := by
      rw [h]
      exact Submodule.mem_top
    rw [hL, hg] at h1
    simp at h1
