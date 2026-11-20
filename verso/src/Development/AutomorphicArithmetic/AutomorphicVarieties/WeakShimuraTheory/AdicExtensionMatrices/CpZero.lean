import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def cpZeroPol {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    (w : ℤ × ℤ) : AddSubgroup A[X] where
  carrier := {p | ∀ n, p.coeff n ∈ 𝒜 w}
  add_mem' := fun {p q} hp hq n => by rw [coeff_add]; exact add_mem (hp n) (hq n)
  zero_mem' := fun n => by rw [coeff_zero]; exact zero_mem _
  neg_mem' := fun {p} hp n => by rw [coeff_neg]; exact neg_mem (hp n)

/- English proof (translation)
Introduce `n` and use `by rw [coeff_one] split_ifs · exact SetLike.one_mem_graded 𝒜 · exact zero_mem _ mul_mem := fun i j p q hp hq n => by rw [coeff_mul] exact Submodule.sum_mem _ fun x _ => SetLike.mul_mem_graded (hp x.1) (hq x.2)`.
-/
private theorem cpZeroPol_graded {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A)
    [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (cpZeroPol 𝒜) where
  one_mem := fun n => by
    rw [coeff_one]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  mul_mem := fun i j p q hp hq n => by
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x _ => SetLike.mul_mem_graded (hp x.1) (hq x.2)

/- English proof (translation)
Introduce `Λ A _ _ _ 𝒜 _ M hM`. Use `haveI := cpZeroPol_graded 𝒜`. Establish `hC : ∀ i j, C (M i j) ∈ cpZeroPol 𝒜 (wt i j)` using `fun i j n => by`. Rewrite using `[coeff_C]`. Use `split_ifs`.

Conclude with `hM i j`. Conclude with `zero_mem _`. Establish `hX : (X : A[X]) ∈ cpZeroPol 𝒜 0` using `fun n => by`. Rewrite using `[coeff_X]`. Use `split_ifs`.

Conclude with `SetLike.one_mem_graded 𝒜`. Conclude with `zero_mem _`. Establish `hE : ∀ i j, M.charmatrix i j ∈ cpZeroPol 𝒜 (wt i j)`. Introduce `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[Matrix.charmatrix_apply_eq]`. Use `sub_mem ?_ (hC i i)` and prove the remaining obligations. Establish `: wt i i = 0` using `by simp [wt]`. Rewrite using `[this]`.

Conclude with `hX`. Rewrite using `[Matrix.charmatrix_apply_ne _ _ _ h]`. Conclude with `neg_mem (hC i j)`. Establish `key : M.charpoly ∈ cpZeroPol 𝒜 0`. Rewrite using `[Matrix.charpoly, Matrix.det_apply]`.

Use `AddSubgroup.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Establish `h0 : ∑ i, wt (σ i) i = 0`. Establish `h1` using `Equiv.sum_comp σ lamW`. Establish `h2` using `Equiv.sum_comp σ muW`. Use `ext`.

Simplify using `only [wt, Prod.fst_sum, Finset.sum_sub_distrib, h1, sub_self, Prod.fst_zero]`. Simplify using `only [wt, Prod.snd_sum, Finset.sum_sub_distrib, h2, sub_self, Prod.snd_zero]`. Establish `hp : ∏ i, M.charmatrix (σ i) i ∈ cpZeroPol 𝒜 (∑ i, wt (σ i) i)` using `SetLike.prod_mem_graded (cpZeroPol 𝒜) (fun i => wt (σ i) i) (fun i => M.charmatrix (σ i) i) fun i _ => hE (σ i) i`. Rewrite `hp` using `[h0]`. Rewrite using `[Units.smul_def]`.

Conclude with `AddSubgroup.zsmul_mem _ hp _`. Conclude with `key`.
-/
theorem UpperTheory.V.Ws.sxCpZero :
    ∀ {Λ A : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] (𝒜 : ℤ × ℤ → Submodule Λ A) [SetLike.GradedMonoid 𝒜] (M : M4 A), (∀ i j, M i j ∈ 𝒜 (wt i j)) → ∀ n, M.charpoly.coeff n ∈ 𝒜 0 := by
  intro Λ A _ _ _ 𝒜 _ M hM
  haveI := cpZeroPol_graded 𝒜
  have hC : ∀ i j, C (M i j) ∈ cpZeroPol 𝒜 (wt i j) := fun i j n => by
    rw [coeff_C]
    split_ifs
    · exact hM i j
    · exact zero_mem _
  have hX : (X : A[X]) ∈ cpZeroPol 𝒜 0 := fun n => by
    rw [coeff_X]
    split_ifs
    · exact SetLike.one_mem_graded 𝒜
    · exact zero_mem _
  have hE : ∀ i j, M.charmatrix i j ∈ cpZeroPol 𝒜 (wt i j) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [Matrix.charmatrix_apply_eq]
      refine sub_mem ?_ (hC i i)
      have : wt i i = 0 := by simp [wt]
      rw [this]; exact hX
    · rw [Matrix.charmatrix_apply_ne _ _ _ h]
      exact neg_mem (hC i j)
  have key : M.charpoly ∈ cpZeroPol 𝒜 0 := by
    rw [Matrix.charpoly, Matrix.det_apply]
    refine AddSubgroup.sum_mem _ fun σ _ => ?_
    have h0 : ∑ i, wt (σ i) i = 0 := by
      have h1 := Equiv.sum_comp σ lamW
      have h2 := Equiv.sum_comp σ muW
      ext
      · simp only [wt, Prod.fst_sum, Finset.sum_sub_distrib, h1, sub_self, Prod.fst_zero]
      · simp only [wt, Prod.snd_sum, Finset.sum_sub_distrib, h2, sub_self, Prod.snd_zero]
    have hp : ∏ i, M.charmatrix (σ i) i ∈ cpZeroPol 𝒜 (∑ i, wt (σ i) i) :=
      SetLike.prod_mem_graded (cpZeroPol 𝒜) (fun i => wt (σ i) i) (fun i => M.charmatrix (σ i) i) fun i _ => hE (σ i) i
    rw [h0] at hp
    rw [Units.smul_def]
    exact AddSubgroup.zsmul_mem _ hp _
  exact key
