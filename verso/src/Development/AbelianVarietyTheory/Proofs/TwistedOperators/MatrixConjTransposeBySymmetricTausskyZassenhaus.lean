import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic

open Polynomial

namespace GlobalTheory.SymmetricSimilarTranspose

/- English proof (translation)
Take `⟨l, h1, h2⟩` from `GlobalTheory.SimilarTranspose.exists_form f hf`. Set `l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k` to `(((Ideal.span {f}).restrictScalars k).liftQ l (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap`. Use `⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y`. Express the relevant statement in the definitionally equal form `l ((X * a) * b) = l (a * (X * b))`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `y hy`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y`. Use `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))` and prove the remaining obligations. Use `hy (Ideal.Quotient.mk (Ideal.span {f}) a)` as an intermediate fact. Rewrite using `[mul_comm]`. Conclude with `this`.

Introduce `x y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y`. Express the relevant statement in the definitionally equal form `l (a * b) = l (b * a)`. Rewrite using `[mul_comm]`.
-/
theorem exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        ∀ x y, B x y = B y x := by
  obtain ⟨l, h1, h2⟩ := GlobalTheory.SimilarTranspose.exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l
      (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l ((X * a) * b) = l (a * (X * b))
    congr 1; ring
  · intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))
    have := hy (Ideal.Quotient.mk (Ideal.span {f}) a)
    rw [mul_comm]
    exact this
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l (a * b) = l (b * a)
    rw [mul_comm]

/- English proof (translation)
Establish `htor : Module.IsTorsion k[X] (Module.AEval' T)` using `Module.AEval.isTorsion_of_finiteDimensional k W T`. Take `⟨ι, _, p, hp, n, ⟨e⟩⟩` from `Module.equiv_directSum_of_isTorsion htor`. Use `choose B hB1 hB2 hB3 using fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)`. Set `π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i})` to `fun i => (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp (Module.AEval'.of T).toLinearMap`. Establish `hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i` using `fun i x => rfl`.

Establish `hT : ∀ i x, π i (T x) = (X : k[X]) • π i x`. Introduce `i x`. Rewrite using `[hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]`. Both sides reduce to the same expression. Use `⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x y`. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]`. Introduce `y hy`. Establish `h0 : e (Module.AEval'.of T y) = 0`. Use extensionality with `i`.

Rewrite using `[← hπ, DirectSum.zero_apply]`. Use `hB2 i _ fun z => ?_` and prove the remaining obligations. Use `hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))` as an intermediate fact. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single i]`.

Rewrite `this` using `[hπ i ((Module.AEval'.of T).symm _)]`. Simplify using `using this`. Introduce `j _ hj`. Rewrite using `[hπ j ((Module.AEval'.of T).symm _)]`. Simplify using `[DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]`.

Simplify using the standard rewrite rules. Simplify using `using h0`. Introduce `x y`. Simplify using `only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => hB3 i _ _`.
-/
theorem exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ x y, B x y = B y x := by
  classical
  have htor : Module.IsTorsion k[X] (Module.AEval' T) :=
    Module.AEval.isTorsion_of_finiteDimensional k W T
  obtain ⟨ι, _, p, hp, n, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion htor
  choose B hB1 hB2 hB3 using
    fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)
  let π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i}) := fun i =>
    (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp
      (Module.AEval'.of T).toLinearMap
  have hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i := fun i x => rfl
  have hT : ∀ i x, π i (T x) = (X : k[X]) • π i x := by
    intro i x
    rw [hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]
    rfl
  refine ⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]
  · intro y hy
    have h0 : e (Module.AEval'.of T y) = 0 := by
      ext i
      rw [← hπ, DirectSum.zero_apply]
      refine hB2 i _ fun z => ?_
      have := hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this
      rw [Finset.sum_eq_single i] at this
      · rw [hπ i ((Module.AEval'.of T).symm _)] at this
        simpa using this
      · intro j _ hj
        rw [hπ j ((Module.AEval'.of T).symm _)]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      · simp
    simpa using h0
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
    exact Finset.sum_congr rfl fun i _ => hB3 i _ _

/- English proof (translation)
Introduce `k ι _ _ _ A`. Take `⟨B, h1, h2, h3⟩` from `exists_bilin (Matrix.toLin' A)`. Take `⟨P, rfl⟩` from `(Matrix.toBilin' (R₁ := k) (n := ι)).surjective B`. Simplify using `only [Matrix.toBilin'_apply', Matrix.toLin'_apply] at h1 h2 h3`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_injective_iff_isUnit]`. Use `(injective_iff_map_eq_zero P.mulVecLin).mpr fun y hy => h2 y fun x => ?_` and prove the remaining obligations. Rewrite `hy` using `[Matrix.mulVecLin_apply]`. Rewrite using `[hy, dotProduct_zero]`. Use extensionality with `i j`.

Use `h3 (Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Simplify using `using this`. Apply `(Matrix.toBilin' (R₁ := k) (n := ι)).injective` to reduce the goal to its premises. Use `LinearMap.ext₂ fun x y => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]`.
-/
theorem main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  obtain ⟨B, h1, h2, h3⟩ := exists_bilin (Matrix.toLin' A)
  obtain ⟨P, rfl⟩ := (Matrix.toBilin' (R₁ := k) (n := ι)).surjective B
  simp only [Matrix.toBilin'_apply', Matrix.toLin'_apply] at h1 h2 h3
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero P.mulVecLin).mpr fun y hy => h2 y fun x => ?_
    rw [Matrix.mulVecLin_apply] at hy
    rw [hy, dotProduct_zero]
  · ext i j
    have := h3 (Pi.single j 1) (Pi.single i 1)
    simpa using this
  · apply (Matrix.toBilin' (R₁ := k) (n := ι)).injective
    refine LinearMap.ext₂ fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, ← h1,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

end GlobalTheory.SymmetricSimilarTranspose
