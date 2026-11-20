import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TraceLogLeLogDet
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Set `W' : Submodule ℂ (EuclideanSpace ℂ ι)` to `W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap`. Set `b` to `stdOrthonormalBasis ℂ W'`. Use `⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `j k`. Establish `h` using `orthonormal_iff_ite.mp b.orthonormal j k`.

Rewrite `h` using `[Submodule.coe_inner, PiLp.inner_apply]`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`. Introduce `v`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Set `w : W'` to `⟨WithLp.toLp 2 v, hv⟩`. Use `⟨fun j => b.repr w j, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Establish `h` using `congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)`. Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h`. Establish `h2 : v i = (w : EuclideanSpace ℂ ι) i` using `rfl`. Rewrite using `[h2, ← h]`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.

Introduce and unpack `⟨x, rfl⟩`. Establish `h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[h]`.

Conclude with `W.sum_mem fun j _ => W.smul_mem _ (b j).2`.
-/
theorem exists_isometry_matrix_range {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2

/- English proof (translation)
Introduce `ι _ _ σ _ τ g hτ hH W hW`. Take `⟨H, hlog, hsum⟩` from `hH`. Take `⟨n, Q, hQ, hmem⟩` from `exists_isometry_matrix_range W`. Establish `hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N`. Introduce `s`.

Establish `: ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x` using `fun j => (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))`. Use `choose x hx using this`. Use `⟨Matrix.of fun i j => x j i, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h` using `congrFun (hx j) i`.

Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Conclude with `h`. Use `choose N hN using hN`. Establish `hNinv : ∀ s, N (τ s) * N s = 1`. Introduce `s`.

Establish `h : Q * (N (τ s) * N s) = Q`. Rewrite using `[← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]`. Establish `h2` using `congrArg (fun X => Qᴴ * X) h`. Simplify `h2` using `only [← Matrix.mul_assoc, hQ, Matrix.one_mul]`. Establish `hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det`.

Introduce `s`. Establish `h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (N s)ᴴ * (Qᴴ * Q) * N s := by`.

Rewrite using `[hN]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [hQ, Matrix.mul_one]`. Rewrite using `[h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`. Use `set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha`.

Establish `hpair : ∀ s, a (τ s) + a s = 0`. Introduce `s`. Establish `h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1`. Rewrite using `[← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]`. Simplify using `only [ha]`.

Rewrite using `[← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]`. Establish `hasum : ∑ s, a s = 0`. Establish `h : ∑ s, (a (τ s) + a s) = 0` using `Finset.sum_eq_zero fun s _ => hpair s`. Rewrite `h` using `[Finset.sum_add_distrib, Equiv.sum_comp τ a]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0`. Rewrite using `[← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]`. Simplify using the standard rewrite rules. Establish `hJ` using `fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ`. Establish `heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s`.

Establish `h` using `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a) (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])`. Conclude with `fun s => h s (Finset.mem_univ s)`. Establish `hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ`. Introduce `s`. Take `⟨M, hM⟩` from `(hJ s).2 (by rw [hdet]; exact heq s)`.

Establish `h1 : N s * N (τ s) = 1` using `mul_eq_one_comm.1 (hNinv s)`. Establish `h2 : (g s)ᴴ * Q = Q * (M * N (τ s))`. Rewrite using `[← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]`. Use `⟨(M * N (τ s))ᴴ, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg Matrix.conjTranspose h2`.

Rewrite `h3` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q]`. Then use the resulting hypothesis. Use `⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩ v hv`. Take `⟨M, hM⟩` from `hadj s`. Rewrite `hv`, the goal using `[LinearMap.mem_ker, Matrix.mulVecLin_apply]`.

Rewrite using `[Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]`. Rewrite using `[Submodule.disjoint_def]`. Introduce `v hv hv'`. Take `⟨x, rfl⟩` from `(hmem v).1 hv`. Rewrite `hv'` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]`.

Rewrite using `[hv', Matrix.mulVec_zero]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Use `Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ, Matrix.one_mulVec, sub_self]`.
-/
theorem ss_of_harm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ)
    (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Harm g → SS (Set.range g) := by
  intro ι _ _ σ _ τ g hτ hH W hW
  obtain ⟨H, hlog, hsum⟩ := hH
  obtain ⟨n, Q, hQ, hmem⟩ := exists_isometry_matrix_range W
  have hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N := by
    intro s
    have : ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x := fun j =>
      (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))
    choose x hx using this
    refine ⟨Matrix.of fun i j => x j i, ?_⟩
    ext i j
    have h := congrFun (hx j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  choose N hN using hN
  have hNinv : ∀ s, N (τ s) * N s = 1 := by
    intro s
    have h : Q * (N (τ s) * N s) = Q := by
      rw [← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]
    have h2 := congrArg (fun X => Qᴴ * X) h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using h2
  have hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det := by
    intro s
    have h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s := by
      calc Qᴴ * ((g s)ᴴ * g s) * Q = (g s * Q)ᴴ * (g s * Q) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (N s)ᴴ * (Qᴴ * Q) * N s := by
            rw [hN]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQ, Matrix.mul_one]
    rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha
  have hpair : ∀ s, a (τ s) + a s = 0 := by
    intro s
    have h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]
    simp only [ha]
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]
  have hasum : ∑ s, a s = 0 := by
    have h : ∑ s, (a (τ s) + a s) = 0 := Finset.sum_eq_zero fun s _ => hpair s
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ a] at h
    linarith
  have htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    simp
  have hJ := fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ
  have heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a)
      (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])
    exact fun s => h s (Finset.mem_univ s)
  have hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ := by
    intro s
    obtain ⟨M, hM⟩ := (hJ s).2 (by rw [hdet]; exact heq s)
    have h1 : N s * N (τ s) = 1 := mul_eq_one_comm.1 (hNinv s)
    have h2 : (g s)ᴴ * Q = Q * (M * N (τ s)) := by
      rw [← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    refine ⟨(M * N (τ s))ᴴ, ?_⟩
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q] at h3
  refine ⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ v hv
    obtain ⟨M, hM⟩ := hadj s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨x, rfl⟩ := (hmem v).1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at hv'
    rw [hv', Matrix.mulVec_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ,
      Matrix.one_mulVec, sub_self]

end GlobalTheory.ClassFin
