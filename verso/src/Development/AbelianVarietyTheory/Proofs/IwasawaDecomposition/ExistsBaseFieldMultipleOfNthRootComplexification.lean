import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankFixedSubmoduleComplexification

open scoped TensorProduct

namespace GlobalTheory.KeyFourth

/- English proof (translation)
Establish `: NeZero n` using `⟨hn.ne'⟩`. Establish `h0` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Establish `h1` using `h0.map_of_injective (algebraMap ℂ R).injective`. Establish `h2` using `h1.pow_sub_pow_eq_prod_sub_mul x y hn`. Rewrite `h2` using `[h, sub_self]`.

Take `⟨ζ, hζ, hz⟩` from `Finset.prod_eq_zero_iff.1 h2.symm`. Rewrite `hζ` using `[Polynomial.mem_nthRootsFinset hn]`. Take `⟨i, -, hi⟩` from `h1.eq_pow_of_pow_eq_one hζ`. Use `⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_pow, hi]`.

Conclude with `sub_eq_zero.1 hz`.
-/
theorem exists_eq_smul_of_pow_eq_pow {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {n : ℕ} (hn : 0 < n) {x y : R} (h : x ^ n = y ^ n) : ∃ z : ℂ, x = z • y := by
  have : NeZero n := ⟨hn.ne'⟩
  have h0 := Complex.isPrimitiveRoot_exp n hn.ne'
  have h1 := h0.map_of_injective (algebraMap ℂ R).injective
  have h2 := h1.pow_sub_pow_eq_prod_sub_mul x y hn
  rw [h, sub_self] at h2
  obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [Polynomial.mem_nthRootsFinset hn] at hζ
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩
  rw [Algebra.smul_def, map_pow, hi]
  exact sub_eq_zero.1 hz

/- English proof (translation)
Introduce `K _ _ A _ _ _ n w C u hn hC hu hw`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)`. Set `T : ℂ ⊗[K] A →ₗ[K] A` to `(TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f`. Establish `hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a` using `fun c a => by simp [T]`. Establish `hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0`.

Introduce `c a hc ha h`. Establish `h1 : (1 : ℂ) ⊗ₜ[K] a = 0`. Use `congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h` as an intermediate fact. Simplify `this` using `[TensorProduct.smul_tmul', hc]`. Establish `h2` using `hT 1 a`.

Rewrite `h2` using `[h1, map_zero, hf, one_smul]`. Conclude with `ha h2.symm`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[zero_pow hn.ne']`.

Conclude with `hne C u hC hu hw.symm`. Establish `hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w}, σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w}`. Introduce `σ x hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Set `S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A` to `Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)`.

Establish `hS : ∀ t, σ.toLinearMap.rTensor A t = S t`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `tmul b v => simp [S]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Take `⟨μ, hμ⟩` from `IsAlgClosed.exists_pow_nat_eq (σ C / C) hn`. Establish `h1 : (S w) ^ n = (μ • w) ^ n`. Rewrite using `[← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul, div_mul_cancel₀ _ hC]`. Simplify using `[S]`.

Take `⟨z, hz⟩` from `exists_eq_smul_of_pow_eq_pow hn h1`. Establish `h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Establish `h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w`.

Rewrite using `[Algebra.smul_def]`. Simplify using `[S]`. Rewrite using `[hS, h2, map_mul, h3, hz, smul_smul, smul_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)`. Take `⟨N, hN, -⟩` from `(GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst`.

Establish `hN0 : N ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hN` using `[Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot]`. Conclude with `hw0 hN`. Take `⟨b, hbN, hb0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hN0`.

Establish `hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w}` using `hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN`. Take `⟨l, hl⟩` from `Submodule.mem_span_singleton.1 hb`. Establish `hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u`. Use `congrArg (· ^ n) hl` as an intermediate fact. Simplify using `only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul', smul_eq_mul] at this`.

Conclude with `this.symm`. Establish `hbn : b ^ n ≠ 0`. Introduce `h`. Establish `h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0`. Rewrite using `[Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]`.

Conclude with `hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)`. Establish `h4` using `congrArg T hpow`. Rewrite `h4` using `[hT, hT, hf, one_smul]`. Establish `h5 : f (l ^ n * C) ≠ 0`. Introduce `h`.

Rewrite `h4` using `[h, zero_smul]`. Conclude with `hbn h4`. Conclude with `⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩`.
-/
theorem exists_eq_smul_pow_of_pow_eq_tmul :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A]
      [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 →
      w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  intro K _ _ A _ _ _ n w C u hn hC hu hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)
  let T : ℂ ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f
  have hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a := fun c a => by simp [T]
  have hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0 := by
    intro c a hc ha h
    have h1 : (1 : ℂ) ⊗ₜ[K] a = 0 := by
      have := congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h
      simpa [TensorProduct.smul_tmul', hc] using this
    have h2 := hT 1 a
    rw [h1, map_zero, hf, one_smul] at h2
    exact ha h2.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact hne C u hC hu hw.symm
  have hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w},
      σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w} := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    let S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
    have hS : ∀ t, σ.toLinearMap.rTensor A t = S t := by
      intro t
      induction t with
      | zero => simp
      | tmul b v => simp [S]
      | add x y hx hy => simp only [map_add, hx, hy]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (σ C / C) hn
    have h1 : (S w) ^ n = (μ • w) ^ n := by
      rw [← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul,
        div_mul_cancel₀ _ hC]
      simp [S]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_pow_eq_pow hn h1
    have h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w := by
      rw [Algebra.smul_def]; rfl
    have h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w := by
      rw [Algebra.smul_def]
      simp [S]
    rw [hS, h2, map_mul, h3, hz, smul_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨N, hN, -⟩ := (GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    rw [Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot] at hN
    exact hw0 hN
  obtain ⟨b, hbN, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w} :=
    hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hb
  have hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u := by
    have := congrArg (· ^ n) hl
    simp only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul',
      smul_eq_mul] at this
    exact this.symm
  have hbn : b ^ n ≠ 0 := by
    intro h
    have h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]
    exact hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)
  have h4 := congrArg T hpow
  rw [hT, hT, hf, one_smul] at h4
  have h5 : f (l ^ n * C) ≠ 0 := by
    intro h
    rw [h, zero_smul] at h4
    exact hbn h4
  exact ⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩

end GlobalTheory.KeyFourth
