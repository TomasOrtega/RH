import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_orthogonal` to reduce the goal to its premises. Conclude with `V.add_mem (h (U.starProjection_apply_mem x)) (((Uᗮ ⊓ V).starProjection_apply_mem x).2)`. Rewrite using `[← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h, ← Submodule.inf_orthogonal, Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_sub]`.

Conclude with `Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x) (((Uᗮ ⊓ V).starProjection_apply_mem x).1)`. Rewrite using `[add_comm, ← sub_sub]`. Use `(Uᗮ ⊓ V)ᗮ.sub_mem ((Uᗮ ⊓ V).sub_starProjection_mem_orthogonal x) ?_` and prove the remaining obligations. Conclude with `Submodule.orthogonal_le (inf_le_left (a := Uᗮ) (b := V)) (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))`.
-/
theorem starProjection_eq_add_inf_orthogonal {n : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : U ≤ V) (x : EuclideanSpace ℂ (Fin n)) :
    V.starProjection x = U.starProjection x + (Uᗮ ⊓ V).starProjection x := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact V.add_mem (h (U.starProjection_apply_mem x))
      (((Uᗮ ⊓ V).starProjection_apply_mem x).2)
  · rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h, ← Submodule.inf_orthogonal,
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h]
    refine ⟨?_, ?_⟩
    · rw [← sub_sub]
      exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x)
        (((Uᗮ ⊓ V).starProjection_apply_mem x).1)
    · rw [add_comm, ← sub_sub]
      refine (Uᗮ ⊓ V)ᗮ.sub_mem ((Uᗮ ⊓ V).sub_starProjection_mem_orthogonal x) ?_
      exact Submodule.orthogonal_le (inf_le_left (a := Uᗮ) (b := V))
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))

/- English proof (translation)
Proceed by induction on `l using Fin.induction with`. Consider the case `zero`. Use `(W 0).starProjection_apply_mem x` as an intermediate fact. Establish `h2 : (W 0).starProjection x = 0`. Establish `h3 : (W 0).starProjection x ∈ (⊥ : Submodule ℂ _)` using `h0 ▸ this`.

Simplify using `using h3`. Simplify using `[h2]`. Consider the case `succ i ih`. Establish `hf : univ.filter (fun k : Fin a => k.val < i.succ.val) = insert i (univ.filter (fun k : Fin a => k.val < i.castSucc.val))`. Use extensionality with `k`.

Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, Finset.sum_insert (by simp), ← ih, add_comm]`. Conclude with `starProjection_eq_add_inf_orthogonal _ _ (hm (Fin.castSucc_le_succ i)) x`.
-/
theorem starProjection_flag_eq_sum {n a : ℕ}
    (W : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h0 : W 0 = ⊥) (hm : Monotone W)
    (l : Fin (a + 1)) (x : EuclideanSpace ℂ (Fin n)) :
    (W l).starProjection x = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val),
      ((W i.castSucc)ᗮ ⊓ W i.succ).starProjection x := by
  induction l using Fin.induction with
  | zero =>
    have := (W 0).starProjection_apply_mem x
    have h2 : (W 0).starProjection x = 0 := by
      have h3 : (W 0).starProjection x ∈ (⊥ : Submodule ℂ _) := h0 ▸ this
      simpa using h3
    simp [h2]
  | succ i ih =>
    have hf : univ.filter (fun k : Fin a => k.val < i.succ.val)
        = insert i (univ.filter (fun k : Fin a => k.val < i.castSucc.val)) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc,
        Fin.ext_iff]
      omega
    rw [hf, Finset.sum_insert (by simp), ← ih, add_comm]
    exact starProjection_eq_add_inf_orthogonal _ _ (hm (Fin.castSucc_le_succ i)) x

/- English proof (translation)
Set `e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)` to `(WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm`. Set `V : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n))` to `fun l => (W l).map e.toLinearMap`. Establish `hV0 : V 0 = ⊥` using `by simp [V, h0]`. Establish `hVm : Monotone V` using `fun l k h => Submodule.map_mono (hm h)`. Establish `hVr : ∀ l, Module.finrank ℂ (V l) = Module.finrank ℂ (W l)` using `fun l => LinearEquiv.finrank_map_eq e (W l)`.

Set `P : Fin a → Submodule ℂ (EuclideanSpace ℂ (Fin n))` to `fun i => (V i.castSucc)ᗮ ⊓ V i.succ`. Establish `hP : ∀ i, Module.finrank ℂ (P i) = j i`. Introduce `i`. Establish `h1` using `Submodule.finrank_add_inf_finrank_orthogonal (hVm (Fin.castSucc_le_succ i))`. Establish `h2` using `hj i`.

Rewrite `h1` using `[hVr, hVr]`. Express the relevant statement in the definitionally equal form `Module.finrank ℂ ↥((V i.castSucc)ᗮ ⊓ V i.succ) = j i`. Use linear arithmetic over natural numbers and integers. Set `b : ∀ i, OrthonormalBasis (Fin (j i)) ℂ (P i)` to `fun i => (stdOrthonormalBasis ℂ (P i)).reindex (finCongr (hP i))`. Set `T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ` to `fun i => Matrix.of fun r c => (b i c : EuclideanSpace ℂ (Fin n)) r`.

Establish `hT : ∀ i k c d, ((T i)ᴴ * T k) c d = inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n))`. Introduce `i k c d`. Simplify using `only [Matrix.mul_apply, conjTranspose_apply, T, of_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Establish `hlt : ∀ i k : Fin a, i < k → ∀ c d, inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) = 0`.

Introduce `i k h c d`. Establish `h1 : (b i c : EuclideanSpace ℂ (Fin n)) ∈ V k.castSucc` using `hVm (Fin.succ_le_castSucc_iff.2 h) (b i c).2.2`. Conclude with `Submodule.inner_right_of_mem_orthogonal h1 (b k d).2.1`. Establish `hproj : ∀ i y, (T i * (T i)ᴴ) *ᵥ y = ((P i).starProjection (e y)).ofLp`. Introduce `i y`.

Rewrite using `[(b i).starProjection_eq_sum_rankOne, ← Matrix.mulVec_mulVec]`. Use extensionality with `r`. Simplify using `only [_root_.sum_apply, InnerProductSpace.rankOne_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [Matrix.mulVec, dotProduct, T, of_apply, conjTranspose_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun s _ => mul_comm _ _`. Use `⟨T, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use extensionality with `c d`. Rewrite using `[hT, ← Submodule.coe_inner, orthonormal_iff_ite.1 (b i).orthonormal, Matrix.one_apply]`. Introduce `i k hik`. Use extensionality with `c d`. Rewrite using `[hT, Matrix.zero_apply]`.

Break down `lt_or_gt_of_ne hik with h | h` into its components or cases. Conclude with `hlt i k h c d`. Rewrite using `[inner_eq_zero_symm]`. Conclude with `hlt k i h d c`. Introduce `l y`.

Establish `h1 : y ∈ W l ↔ e y ∈ V l`. Simplify using `[V]`. Rewrite using `[h1, ← Submodule.starProjection_eq_self_iff, starProjection_flag_eq_sum V hV0 hVm, Matrix.sum_mulVec]`. Simplify using `only [hproj]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h2` using `congrArg WithLp.ofLp h`. Rewrite `h2` using `[WithLp.ofLp_sum]`. Conclude with `h2`. Introduce `h`.

Apply `WithLp.ofLp_injective 2` to reduce the goal to its premises. Rewrite using `[WithLp.ofLp_sum]`. Conclude with `h`.
-/
theorem exists_orthonormal_frame_of_flag (n a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hj : ∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) :
    ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧
      (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun l => (W l).map e.toLinearMap
  have hV0 : V 0 = ⊥ := by simp [V, h0]
  have hVm : Monotone V := fun l k h => Submodule.map_mono (hm h)
  have hVr : ∀ l, Module.finrank ℂ (V l) = Module.finrank ℂ (W l) :=
    fun l => LinearEquiv.finrank_map_eq e (W l)
  let P : Fin a → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun i => (V i.castSucc)ᗮ ⊓ V i.succ
  have hP : ∀ i, Module.finrank ℂ (P i) = j i := by
    intro i
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Fin.castSucc_le_succ i))
    have h2 := hj i
    rw [hVr, hVr] at h1
    change Module.finrank ℂ ↥((V i.castSucc)ᗮ ⊓ V i.succ) = j i
    omega
  let b : ∀ i, OrthonormalBasis (Fin (j i)) ℂ (P i) :=
    fun i => (stdOrthonormalBasis ℂ (P i)).reindex (finCongr (hP i))
  let T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ :=
    fun i => Matrix.of fun r c => (b i c : EuclideanSpace ℂ (Fin n)) r
  have hT : ∀ i k c d, ((T i)ᴴ * T k) c d
      = inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) := by
    intro i k c d
    simp only [Matrix.mul_apply, conjTranspose_apply, T, of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hlt : ∀ i k : Fin a, i < k → ∀ c d,
      inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) = 0 := by
    intro i k h c d
    have h1 : (b i c : EuclideanSpace ℂ (Fin n)) ∈ V k.castSucc :=
      hVm (Fin.succ_le_castSucc_iff.2 h) (b i c).2.2
    exact Submodule.inner_right_of_mem_orthogonal h1 (b k d).2.1
  have hproj : ∀ i y, (T i * (T i)ᴴ) *ᵥ y = ((P i).starProjection (e y)).ofLp := by
    intro i y
    rw [(b i).starProjection_eq_sum_rankOne, ← Matrix.mulVec_mulVec]
    ext r
    simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, WithLp.ofLp_sum,
      Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.mulVec, dotProduct, T, of_apply, conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    ext c d
    rw [hT, ← Submodule.coe_inner, orthonormal_iff_ite.1 (b i).orthonormal, Matrix.one_apply]
  · intro i k hik
    ext c d
    rw [hT, Matrix.zero_apply]
    rcases lt_or_gt_of_ne hik with h | h
    · exact hlt i k h c d
    · rw [inner_eq_zero_symm]
      exact hlt k i h d c
  · intro l y
    have h1 : y ∈ W l ↔ e y ∈ V l := by
      simp [V]
    rw [h1, ← Submodule.starProjection_eq_self_iff, starProjection_flag_eq_sum V hV0 hVm,
      Matrix.sum_mulVec]
    simp only [hproj]
    constructor
    · intro h
      have h2 := congrArg WithLp.ofLp h
      rw [WithLp.ofLp_sum] at h2
      exact h2
    · intro h
      apply WithLp.ofLp_injective 2
      rw [WithLp.ofLp_sum]
      exact h

end GlobalTheory
