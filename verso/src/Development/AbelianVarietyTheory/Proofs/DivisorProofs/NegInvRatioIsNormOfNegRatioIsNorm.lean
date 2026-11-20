import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU.NormSwap

/- English proof (translation)
Introduce `F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε`. Set `B` to `Algebra.TensorProduct.basis R b`. Establish `hB : ∀ i, B i = 1 ⊗ₜ[F] b i` using `fun i => Algebra.TensorProduct.basis_apply b i`. Establish `h0 : B 0 = 1` using `by rw [hB, hb0]; rfl`. Establish `h1 : B 1 * B 1 = algebraMap F R δ • B 0`.

Rewrite using `[hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, one_mul, algebraMap_smul]`. Establish `hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e` using `fun r e => rfl`. Establish `key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)`. Introduce `x y`. Establish `e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1`.

Rewrite using `[map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0, map_one, TensorProduct.tmul_neg, sub_eq_add_neg]`. Rewrite using `[e]`. Rewrite `h1`, the goal using `[h0]`. Generalize the expression as in `algebraMap F R δ = d at h1 ⊢`. Simplify using `only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢`.

Take the linear combination `(-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1`. Establish `hz` using `B.sum_repr t`. Rewrite `hz` using `[Fin.sum_univ_two]`. Use `set p₀ := B.repr t 0`. Use `set q₀ := B.repr t 1`.

Rewrite `hε` using `[← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add, ← map_mul]`. Establish `hinj : Function.Injective (algebraMap R (R ⊗[F] E))`. Use `Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E) (algebraMap F E).injective` as an intermediate fact. Introduce `x y hxy`. Apply `this` to reduce the goal to its premises.

Simplify `hxy` using `[Algebra.TensorProduct.algebraMap_apply]`. Establish `h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0` using `hinj (by rw [hε, map_zero])`. Use `set c := algebraMap F R (f₂ / f₁)`. Establish `hca : c * algebraMap F R (f₁ / f₂) = 1`. Rewrite using `[← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]`.

Use `⟨c * p₀, c * q₀, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg]`. Take the linear combination `(-c ^ 2) * h + ε * c * hca`.
-/
theorem neg_inv_ratio_norm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  intro F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  have hz := B.sum_repr t
  rw [Fin.sum_univ_two] at hz
  set p₀ := B.repr t 0
  set q₀ := B.repr t 1
  rw [← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add, ← map_mul] at hε
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective
    intro x y hxy
    apply this
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  have h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0 :=
    hinj (by rw [hε, map_zero])
  set c := algebraMap F R (f₂ / f₁)
  have hca : c * algebraMap F R (f₁ / f₂) = 1 := by
    rw [← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]
  refine ⟨c * p₀, c * q₀, ?_⟩
  rw [map_neg]
  linear_combination (-c ^ 2) * h + ε * c * hca

end GlobalTheory.PlaneSU.NormSwap
