import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

/- English proof (translation)
Simplify using `only [Matrix.reindex_apply]`. Conclude with `Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm`.
-/
theorem reindex_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι) (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

/- English proof (translation)
Set `f : (Fin n → K) ≃ₗ[K] (ι → K)` to `LinearEquiv.funCongrLeft K K e.symm`. Establish `hmv : ∀ w : Fin n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm`. Introduce `w`. Rewrite using `[Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Establish `key : ∀ (x : Fin n → K) (S : Set (Fin n → K)), x ∘ e.symm ∈ Submodule.span K ((fun w : Fin n → K => w ∘ e.symm) '' S) ↔ x ∈ Submodule.span K S`. Introduce `x S`. Establish `h1 : (fun w : Fin n → K => w ∘ e.symm) = ⇑(f.toLinearMap)` using `rfl`.

Rewrite using `[h1, Submodule.span_image, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Establish `hyx : y = x` using `f.injective hxy`. Conclude with `hyx ▸ hy`.

Introduce `hx`. Conclude with `⟨x, hx, rfl⟩`. Unfold `FlagC`. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Use `show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈ Submodule.span K ((fun a => v a ∘ e.symm) '' {a | a < b}) ↔ _`.

Rewrite using `[hmv, show (fun a => v a ∘ e.symm) '' {a | a < b} = (fun w : Fin n → K => w ∘ e.symm) '' (v '' {a | a < b}) from (Set.image_image (fun w : Fin n → K => w ∘ e.symm) v {a | a < b}).symm]`. Conclude with `key (M *ᵥ v b - v b) _`.
-/
private theorem flagC_reindex_iff {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Fin n ≃ ι) (M : Matrix (Fin n) (Fin n) K) (v : Fin m → Fin n → K) :
    FlagC (Matrix.reindex e e M) (fun b => v b ∘ e.symm) ↔ FlagC M v := by
  let f : (Fin n → K) ≃ₗ[K] (ι → K) := LinearEquiv.funCongrLeft K K e.symm
  have hmv : ∀ w : Fin n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm := by
    intro w
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext j
    simp
  have key : ∀ (x : Fin n → K) (S : Set (Fin n → K)),
      x ∘ e.symm ∈ Submodule.span K ((fun w : Fin n → K => w ∘ e.symm) '' S) ↔ x ∈ Submodule.span K S := by
    intro x S
    have h1 : (fun w : Fin n → K => w ∘ e.symm) = ⇑(f.toLinearMap) := rfl
    rw [h1, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := f.injective hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold FlagC
  refine forall_congr' fun b => ?_
  show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈
      Submodule.span K ((fun a => v a ∘ e.symm) '' {a | a < b}) ↔ _
  rw [hmv, show (fun a => v a ∘ e.symm) '' {a | a < b} =
      (fun w : Fin n → K => w ∘ e.symm) '' (v '' {a | a < b}) from
      (Set.image_image (fun w : Fin n → K => w ∘ e.symm) v {a | a < b}).symm]
  exact key (M *ᵥ v b - v b) _

/- English proof (translation)
Rewrite using `[mem_Ssub_iff_flagC σ J θ P g]`. Establish `hU : (Matrix.reindex e e (cmp2 σ J θ g))ᵀ * Matrix.reindex e e (jm1 J θ) * ((g1 : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (jm1 J θ)`. Rewrite using `[hg1, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit σ J θ hθ g]`. Establish `hJ' : IsUnit (Matrix.reindex e e (jm1 J θ)).det`. Rewrite using `[Matrix.det_reindex_self]` and apply the resulting hypothesis.

Rewrite using `[← frame_mem_sG g1 Q _ _ hJ' hU (fun b => pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) (fun b => pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) l hl hy1 hy2, hg1]`. Conclude with `and_congr (flagC_reindex_iff e _ _).symm (flagC_reindex_iff e _ _).symm`.
-/
theorem mem_Ssub_iff_sG (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) {r k : ℕ} (e : Fin n ≃ Idx r k)
    (hJ : IsUnit (jm1 J θ).det) (P : Frame E n r) (Q : GL (Idx r k) R) (l : Fin (r + 1) → R)
    (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) *ᵥ
      (pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) R)ᵀ *ᵥ ((Matrix.reindex e e (jm1 J θ))ᵀ *ᵥ
      (pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)) = l b • Pi.single (pf b) 1)
    (g : HA R σ J) (g1 : GL (Idx r k) R)
    (hg1 : (g1 : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (cmp1 σ J θ g)) :
    g ∈ Ssub R σ J P ↔ Q⁻¹ * g1 * Q ∈ sG R r k := by
  rw [mem_Ssub_iff_flagC σ J θ P g]
  have hU : (Matrix.reindex e e (cmp2 σ J θ g))ᵀ * Matrix.reindex e e (jm1 J θ) *
      ((g1 : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (jm1 J θ) := by
    rw [hg1, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit σ J θ hθ g]
  have hJ' : IsUnit (Matrix.reindex e e (jm1 J θ)).det := by
    rwa [Matrix.det_reindex_self]
  rw [← frame_mem_sG g1 Q _ _ hJ' hU (fun b => pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)
    (fun b => pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) l hl hy1 hy2, hg1]
  exact and_congr (flagC_reindex_iff e _ _).symm (flagC_reindex_iff e _ _).symm

end MassDataIdxStIm
