import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Use `set b := Module.finBasis ℚ L`. Set `M : Matrix (L →+* K) (Fin (Module.finrank ℚ L)) K` to `Matrix.of fun σ i => σ (b i)`. Establish `hD : LinearIndependent K (fun σ : L →+* K => (σ : L → K))`. Establish `h` using `linearIndependent_monoidHom L K`. Establish `hinj : Function.Injective (fun σ : L →+* K => (σ.toMonoidHom : L →* K))`.

Introduce `σ τ h'`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun h' x`. Conclude with `h.comp _ hinj`. Establish `hrow : LinearIndependent K M.row`.

Rewrite `hD`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `hD g` to reduce the goal to its premises. Establish `hb : ∀ i, ∑ σ, g σ * σ (b i) = 0`. Introduce `i`.

Use `congr_fun hg i` as an intermediate fact. Simplify `this` using `[M, Matrix.row, Finset.sum_apply]`. Use function extensionality and compare the values at `x`. Rewrite using `[← b.sum_repr x]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum]`.

Establish `: ∀ σ : L →+* K, ∀ i, σ (b.repr x i • b i) = (b.repr x i : K) * σ (b i)`. Introduce `σ i`. Rewrite using `[Algebra.smul_def, map_mul]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[this, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h2 : ∑ σ : L →+* K, g σ * ((b.repr x i : K) * σ (b i)) = (b.repr x i : K) * ∑ σ : L →+* K, g σ * σ (b i)`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => by ring`.

Rewrite using `[h2, hb i, mul_zero]`. Establish `hrank : M.rank = Fintype.card (L →+* K)` using `hrow.rank_matrix`. Establish `htop : LinearMap.range M.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]`.

Establish `hz : z ∈ LinearMap.range M.mulVecLin` using `by rw [htop]; trivial`. Take `⟨y, hy⟩` from `hz`. Use `⟨y, fun σ => ?_⟩` and prove the remaining obligations. Use `congr_fun hy σ` as an intermediate fact. Simplify `this` using `[M, Matrix.mulVec, dotProduct]`.
-/
theorem embeddings_eval_onto (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K]
    (z : (L →+* K) → K) :
    ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K,
      ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  classical
  set b := Module.finBasis ℚ L
  let M : Matrix (L →+* K) (Fin (Module.finrank ℚ L)) K := Matrix.of fun σ i => σ (b i)

  have hD : LinearIndependent K (fun σ : L →+* K => (σ : L → K)) := by
    have h := linearIndependent_monoidHom L K
    have hinj : Function.Injective (fun σ : L →+* K => (σ.toMonoidHom : L →* K)) := by
      intro σ τ h'
      ext x
      exact DFunLike.congr_fun h' x
    exact h.comp _ hinj
  have hrow : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hD ⊢
    intro g hg
    apply hD g
    have hb : ∀ i, ∑ σ, g σ * σ (b i) = 0 := by
      intro i
      have := congr_fun hg i
      simpa [M, Matrix.row, Finset.sum_apply] using this
    funext x
    rw [← b.sum_repr x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum]
    have : ∀ σ : L →+* K, ∀ i, σ (b.repr x i • b i) = (b.repr x i : K) * σ (b i) := by
      intro σ i
      rw [Algebra.smul_def, map_mul]
      simp
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ σ : L →+* K, g σ * ((b.repr x i : K) * σ (b i)) =
        (b.repr x i : K) * ∑ σ : L →+* K, g σ * σ (b i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h2, hb i, mul_zero]
  have hrank : M.rank = Fintype.card (L →+* K) := hrow.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have hz : z ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, fun σ => ?_⟩
  have := congr_fun hy σ
  simpa [M, Matrix.mulVec, dotProduct] using this

end GlobalTheory
