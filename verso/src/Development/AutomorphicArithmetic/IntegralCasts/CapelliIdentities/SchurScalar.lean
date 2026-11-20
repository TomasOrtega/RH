import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi17.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qi17.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qi17.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qi17.IsIrrSub r ⊤

/- English proof (translation)
Introduce `Γ k _ _ _ n r hr g hg`. Take `⟨hne, -, hmin⟩` from `hr`. Use `haveI : Nontrivial (Fin n → k) := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`.

Conclude with `hne (Subsingleton.elim _ _)`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))`. Establish `hinv : UpperTheory.Reformulated.B.Qi17.IsInv r (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c)`. Introduce `s v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`.

Establish `h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)`. Rewrite using `[← Units.val_mul, ← Units.val_mul, hg s]`. Rewrite using `[Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]`. Establish `htop` using `(hmin _ le_top hinv).resolve_left hc`. Establish `hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k)`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Rewrite `hv` using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hgc` using `[zero_smul]`.

Take `⟨v, hv⟩` from `exists_ne (0 : Fin n → k)`. Apply `hv` to reduce the goal to its premises. Establish `h1 : (1 : Matrix (Fin n) (Fin n) k) = 0`. Rewrite using `[← g.mul_inv, hgc, zero_mul]`. Rewrite using `[← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]`.

Conclude with `⟨Units.mk0 c hc0, hgc⟩`.
-/
theorem UpperTheory.Reformulated.B.Qi17.schur_scalar :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qi17.IsIrr r →
        ∀ (g : GL (Fin n) k),
          (∀ (s : Γ), (r : Γ → GL (Fin n) k) s * g = g * (r : Γ → GL (Fin n) k) s) →
            ∃ (c : kˣ), (↑g : Matrix (Fin n) (Fin n) k) = (↑c : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n r hr g hg
  obtain ⟨hne, -, hmin⟩ := hr
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hinv : UpperTheory.Reformulated.B.Qi17.IsInv r
      (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c) := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    have h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
        = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hg s]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have htop := (hmin _ le_top hinv).resolve_left hc
  have hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c := by
      rw [htop]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgc
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    apply hv
    have h1 : (1 : Matrix (Fin n) (Fin n) k) = 0 := by
      rw [← g.mul_inv, hgc, zero_mul]
    rw [← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]
  exact ⟨Units.mk0 c hc0, hgc⟩
