import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Use `set b := bas A hG`. Use `set φ : A.K →ₗ[F] A.K := Matrix.toLin b b M with hφ`. Establish `hMφ : LinearMap.toMatrix b b φ = M` using `by simp [hφ]`. Establish `hlm : ∀ x : A.K, Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (Algebra.lmul F A.K x)` using `fun x => rfl`. Establish `hτ : φ ∘ₗ Algebra.lmul F A.K τ = Algebra.lmul F A.K τ ∘ₗ φ`.

Apply `(LinearMap.toMatrix b b).injective` to reduce the goal to its premises. Rewrite using `[LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hMφ, ← hlm, leftMul_tau]`. Conclude with `hM`. Establish `hτx : ∀ x, φ (τ * x) = τ * φ x` using `fun x => by`. Use `congrArg (fun f => f x) hτ` as an intermediate fact.

Simplify using `using this`. Establish `hpow : ∀ (n : ℕ) x, φ (τ ^ n * x) = τ ^ n * φ x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`.

Simplify using the standard rewrite rules. Consider the case `succ n ih => intro x`. Rewrite using `[pow_succ', mul_assoc, hτx, ih, ← mul_assoc]`. Establish `hall : ∀ k x, φ (k * x) = k * φ x`. Introduce `k x`.

Rewrite using `[← b.sum_repr k, Finset.sum_mul, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_mul_assoc, bas_apply, hpow]`. Use `⟨φ 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hMφ, hlm]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']`. Rewrite using `[mul_comm, ← hall, mul_one]`.
-/
theorem exists_leftMul_of_comm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
    (hG : A.IsGen τ p) (M : Matrix (Fin r) (Fin r) F) (hM : M * companion p = companion p * M) :
    ∃ k : A.K, M = Algebra.leftMulMatrix (bas A hG) k := by
  set b := bas A hG
  set φ : A.K →ₗ[F] A.K := Matrix.toLin b b M with hφ
  have hMφ : LinearMap.toMatrix b b φ = M := by simp [hφ]
  have hlm : ∀ x : A.K, Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (Algebra.lmul F A.K x) := fun x => rfl
  have hτ : φ ∘ₗ Algebra.lmul F A.K τ = Algebra.lmul F A.K τ ∘ₗ φ := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hMφ, ← hlm, leftMul_tau]
    exact hM
  have hτx : ∀ x, φ (τ * x) = τ * φ x := fun x => by
    have := congrArg (fun f => f x) hτ
    simpa using this
  have hpow : ∀ (n : ℕ) x, φ (τ ^ n * x) = τ ^ n * φ x := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', mul_assoc, hτx, ih, ← mul_assoc]
  have hall : ∀ k x, φ (k * x) = k * φ x := by
    intro k x
    rw [← b.sum_repr k, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_mul_assoc, bas_apply, hpow]
  refine ⟨φ 1, ?_⟩
  rw [← hMφ, hlm]
  congr 1
  ext x
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [mul_comm, ← hall, mul_one]

/- English proof (translation)
Introduce `F E _ _ _ _ A r τ p hG t ht`. Establish `ht' : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)`. Establish `h1 : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (t : Matrix (Fin r) (Fin r) F) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2 : (t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.mul_one]`. Use `_ = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * ((t : Matrix (Fin r) (Fin r) F) * companion p) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by`. Rewrite using `[ht]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Take `⟨k, hk⟩` from `exists_leftMul_of_comm A hG _ ht`. Take `⟨k', hk'⟩` from `exists_leftMul_of_comm A hG _ ht'`.

Establish `hinj` using `Algebra.leftMulMatrix_injective (bas A hG)`. Establish `e1 : k * k' = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, ← hk, ← hk', ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `e2 : k' * k = 1` using `by rw [mul_comm, e1]`.

Use `⟨⟨k, k', e1, e2⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[tm_coe]`. Conclude with `hk.symm`.
-/
theorem centr : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  intro F E _ _ _ _ A r τ p hG t ht
  have ht' : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p =
      companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
    have h1 : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (t : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p
        = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p *
            ((t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * ((t : Matrix (Fin r) (Fin r) F) * companion p) *
            ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [ht]; simp only [Matrix.mul_assoc]
      _ = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨k, hk⟩ := exists_leftMul_of_comm A hG _ ht
  obtain ⟨k', hk'⟩ := exists_leftMul_of_comm A hG _ ht'
  have hinj := Algebra.leftMulMatrix_injective (bas A hG)
  have e1 : k * k' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hk, ← hk', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : k' * k = 1 := by rw [mul_comm, e1]
  refine ⟨⟨k, k', e1, e2⟩, ?_⟩
  apply Units.ext
  rw [tm_coe]
  exact hk.symm

end GlobalTheory.JR.LinDesc
