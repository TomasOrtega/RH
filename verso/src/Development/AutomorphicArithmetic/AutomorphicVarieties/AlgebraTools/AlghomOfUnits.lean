import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `K E _ _ _ σ _ _ d _ _ _ e hmul horth hst hsum`. Set `f : (∀ s, Matrix (d s) (d s) K) → E` to `fun M => ∑ s, ∑ i, ∑ k, M s i k • e s i k`. Establish `hadd : ∀ M N, f (M + N) = f M + f N`. Introduce `M N`. Simplify using `only [f, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]`.

Establish `hsmul : ∀ (c : K) M, f (c • M) = c • f M`. Introduce `c M`. Simplify using `only [f, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`. Establish `key : ∀ (N : ∀ s, Matrix (d s) (d s) K) s i j (a : K), (a • e s i j) * f N = ∑ k, (a * N s j k) • e s i k`. Introduce `N s i j a`.

Simplify using `only [f]`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single s]`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single j]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm, hmul]`. Introduce `l _ hl`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, horth s i j l k (Ne.symm hl), smul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `t _ ht`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, hst s t i j l k (Ne.symm ht), smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `hm : ∀ M N, f (M * N) = f M * f N`. Introduce `M N`. Establish `: f M * f N = ∑ s, ∑ i, ∑ j, ∑ k, (M s i j * N s j k) • e s i k` using `by show (∑ s, ∑ i, ∑ k, M s i k • e s i k) * f N = _`. Simplify using `only [Finset.sum_mul, key]`. Rewrite using `[this]`.

Simplify using `only [f, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm`. Establish `h1 : f 1 = 1`. Simplify using `only [f, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Conclude with `hsum`. Set `L : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E` to `{ toFun := f, map_add' := hadd, map_smul' := hsmul }`. Use `⟨AlgHom.ofLinearMap L h1 hm, ?_⟩` and prove the remaining obligations. Introduce `s i k`. Use `show f (Pi.single s (Matrix.single i k 1)) = e s i k`.

Simplify using `only [f]`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[Pi.single_eq_same]`. Simplify using `only [Matrix.single_apply, ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_eq_single i]`.

Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Conclude with `fun h => hb h.2.symm`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Conclude with `fun h => hb h.1.symm`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `t _ ht`. Simplify using `[Pi.single_eq_of_ne ht]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem UpperTheory.V.AlgebraTools.alghom_of_units :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (e : ∀ s, d s → d s → E), (∀ s i j k, e s i j * e s j k = e s i k) → (∀ s i j k l, j ≠ k → e s i j * e s k l = 0) → (∀ s t i j k l, s ≠ t → e s i j * e t k l = 0) → ∑ s, ∑ i, e s i i = 1 → ∃ j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E, ∀ s i k, j (Pi.single s (single i k 1)) = e s i k := by
  intro K E _ _ _ σ _ _ d _ _ _ e hmul horth hst hsum
  let f : (∀ s, Matrix (d s) (d s) K) → E := fun M => ∑ s, ∑ i, ∑ k, M s i k • e s i k
  have hadd : ∀ M N, f (M + N) = f M + f N := by
    intro M N
    simp only [f, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : K) M, f (c • M) = c • f M := by
    intro c M
    simp only [f, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have key : ∀ (N : ∀ s, Matrix (d s) (d s) K) s i j (a : K),
      (a • e s i j) * f N = ∑ k, (a * N s j k) • e s i k := by
    intro N s i j a
    simp only [f]
    rw [Finset.mul_sum, Finset.sum_eq_single s]
    · rw [Finset.mul_sum, Finset.sum_eq_single j]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_smul_comm, hmul]
      · intro l _ hl
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [smul_mul_smul_comm, horth s i j l k (Ne.symm hl), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t _ ht
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [smul_mul_smul_comm, hst s t i j l k (Ne.symm ht), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hm : ∀ M N, f (M * N) = f M * f N := by
    intro M N
    have : f M * f N = ∑ s, ∑ i, ∑ j, ∑ k, (M s i j * N s j k) • e s i k := by
      show (∑ s, ∑ i, ∑ k, M s i k • e s i k) * f N = _
      simp only [Finset.sum_mul, key]
    rw [this]
    simp only [f, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have h1 : f 1 = 1 := by
    simp only [f, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hsum
  let L : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E :=
    { toFun := f, map_add' := hadd, map_smul' := hsmul }
  refine ⟨AlgHom.ofLinearMap L h1 hm, ?_⟩
  intro s i k
  show f (Pi.single s (Matrix.single i k 1)) = e s i k
  simp only [f]
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same]
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [if_neg]
        exact fun h => hb h.2.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      exact fun h => hb h.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ _) h
