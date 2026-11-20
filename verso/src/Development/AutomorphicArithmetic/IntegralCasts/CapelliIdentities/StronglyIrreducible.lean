import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.gm :
    {G R : Type} → [inst : Group G] → [inst_1 : CommRing R] → {n : ℕ} → (G →* GL (Fin n) R) → G → Matrix (Fin n) (Fin n) R :=
    fun {G R : Type} [Group G] [CommRing R] {n : ℕ} (r : G →* GL (Fin n) R) (g : G) ↦
      (↑((r : G → GL (Fin n) R) g) : Matrix (Fin n) (Fin n) R)

noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr :
    {G κ : Type} → [inst : Group G] → [inst_1 : Field κ] → {n : ℕ} → (G →* GL (Fin n) κ) → Prop :=
    fun {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) ↦
      ∀ (W : Submodule κ (Fin n → κ)) (S : Subgroup G),
        S.FiniteIndex → (∀ (g : G), g ∈ S ↔ ∀ v ∈ W, (UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/- English proof (translation)
Introduce `G κ _ _ n r h P W S hS hW`. Establish `h1 : ∀ v : Fin n → κ, ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec ((P : Matrix (Fin n) (Fin n) κ).mulVec v) = v`. Introduce `v`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `h2 : ∀ v : Fin n → κ, (P : Matrix (Fin n) (Fin n) κ).mulVec (((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v) = v`.

Introduce `v`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `h3 : ∀ (g : G) (v : Fin n → κ), (UpperTheory.Reformulated.B.StronglyIrreducible.gm ((MulEquiv.toMonoidHom ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) g).mulVec v = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec ((UpperTheory.Reformulated.B.Strong …`. Introduce `g v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.

Express the relevant statement in the definitionally equal form `(((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin n) κ)) : Matrix (Fin n) (Fin n) κ).mulVec v = _`. Rewrite using `[inv_inv, Units.val_mul, Units.val_mul]`. Establish `hmem : ∀ v : Fin n → κ, v ∈ W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) ↔ ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v ∈ W` using `fun v => Iff.rfl`. Establish `key` using `h (W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ))) S hS (by`. Introduce `g`.

Rewrite using `[hW g]`. Prove the components needed by the constructor for the conclusion. Introduce `hg v hv`. Use `hg _ ((hmem v).1 hv)` as an intermediate fact. Rewrite `this` using `[h3, h2]`.

Conclude with `(hmem _).2 this`. Introduce `hg v hv`. Rewrite using `[h3]`. Apply `(hmem _).1` to reduce the goal to its premises. Apply `hg` to reduce the goal to its premises.

Rewrite using `[hmem, h1]`. Conclude with `hv)`. Break down `key with key | key` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `v hv`. Establish `hv' : (P : Matrix (Fin n) (Fin n) κ).mulVec v ∈ W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ))`. Rewrite using `[hmem, h1]`. Conclude with `hv`. Rewrite `hv'` using `[key, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_bot, ← h1 v, hv', Matrix.mulVec_zero]`. Use `right`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← h1 v]`.

Apply `(hmem _).1` to reduce the goal to its premises. Rewrite using `[key]`. Conclude with `Submodule.mem_top`.
-/
theorem UpperTheory.Reformulated.B.StronglyIrreducible.strongIrr_conj :
    ∀ {G κ : Type} [inst : Group G] [inst_1 : Field κ] {n : ℕ} (r : G →* GL (Fin n) κ),
      UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr r →
        ∀ (P : GL (Fin n) κ),
          UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr
            ((MulEquiv.toMonoidHom ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) := by
  intro G κ _ _ n r h P W S hS hW
  have h1 : ∀ v : Fin n → κ, ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
      ((P : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h2 : ∀ v : Fin n → κ, (P : Matrix (Fin n) (Fin n) κ).mulVec
      (((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have h3 : ∀ (g : G) (v : Fin n → κ),
      (UpperTheory.Reformulated.B.StronglyIrreducible.gm ((MulEquiv.toMonoidHom
        ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) g).mulVec v
      = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
        ((UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec ((P : Matrix (Fin n) (Fin n) κ).mulVec v)) := by
    intro g v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change (((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin n) κ)) : Matrix (Fin n) (Fin n) κ).mulVec v = _
    rw [inv_inv, Units.val_mul, Units.val_mul]
  have hmem : ∀ v : Fin n → κ,
      v ∈ W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) ↔
        ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v ∈ W := fun v => Iff.rfl
  have key := h (W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)))
    S hS (by
      intro g
      rw [hW g]
      constructor
      · intro hg v hv
        have := hg _ ((hmem v).1 hv)
        rw [h3, h2] at this
        exact (hmem _).2 this
      · intro hg v hv
        rw [h3]
        apply (hmem _).1
        apply hg
        rw [hmem, h1]
        exact hv)
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have hv' : (P : Matrix (Fin n) (Fin n) κ).mulVec v ∈
        W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) := by
      rw [hmem, h1]
      exact hv
    rw [key, Submodule.mem_bot] at hv'
    rw [Submodule.mem_bot, ← h1 v, hv', Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    rw [← h1 v]
    apply (hmem _).1
    rw [key]
    exact Submodule.mem_top
