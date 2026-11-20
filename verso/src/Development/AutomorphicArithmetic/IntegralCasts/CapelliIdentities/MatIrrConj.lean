import Mathlib

noncomputable def UpperTheory.Reformulated.B.Ua5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/- English proof (translation)
Introduce `G R _ _ m U a a' h hconj hirr W hW`. Establish `hcancel : ∀ w : Fin m → R, (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hmem : ∀ v : Fin m → R, v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔ (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W` using `fun v => Iff.rfl`.

Establish `hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)), (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R))`. Introduce `g hg v hv`. Rewrite `hv`, the goal using `[hmem]`. Rewrite using `[hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]`. Conclude with `hW g hg _ hv`.

Break down `hirr _ hinv with hbot | htop` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Establish `h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R))`.

Rewrite using `[hmem, hcancel]`. Conclude with `hw`. Rewrite `h1` using `[hbot, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot, ← hcancel w, h1, Matrix.mulVec_zero]`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R))`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Rewrite `h1` using `[hmem, hcancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.Ua5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Ua5.MatIrr U a → UpperTheory.Reformulated.B.Ua5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hbot | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [hmem, hcancel]
      exact hw
    rw [hbot, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← hcancel w, h1, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [htop]
      exact Submodule.mem_top
    rwa [hmem, hcancel] at h1
