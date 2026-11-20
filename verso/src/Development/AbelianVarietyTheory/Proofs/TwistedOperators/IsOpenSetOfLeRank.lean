import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
open Matrix Topology

namespace GlobalTheory

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h`. Use `choose v hv using fun i => (w i).2`. Set `B : Matrix n (Fin κ) k` to `Matrix.of fun j i => v i j`. Establish `hw' : LinearIndependent k (fun i => (w i : m → k))` using `hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)`. Establish `hcol : (x * B).col = fun i => (w i : m → k)`.

Use function extensionality and compare the values at `i j`. Rewrite using `[← hv i]`. Simplify using `[B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]`. Establish `hinj : Function.Injective (x * B).mulVec`. Rewrite using `[Matrix.mulVec_injective_iff, hcol]`.

Conclude with `hw'`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B)) (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))`. Use `⟨LinearMap.toMatrix' g, B, ?_⟩` and prove the remaining obligations. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`.

Rewrite using `[Matrix.mul_assoc, this]`.
-/
theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `x hx`. Take `⟨A, B, hAB⟩` from `exists_mul_mul_eq_one_of_le_rank x hx`. Use `⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hu : IsUnit (A * y * B)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)`. Establish `h1` using `Matrix.rank_of_isUnit _ hu`. Rewrite `h1` using `[Fintype.card_fin]`. Express the relevant statement in the definitionally equal form `κ ≤ y.rank`. Rewrite using `[← h1]`.

Conclude with `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)`. Establish `hc : Continuous fun y : Matrix m n k => (A * y * B).det` using `((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det`. Conclude with `isOpen_ne.preimage hc`. Simplify using `[hAB]`.
-/
theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
