import Mathlib

open Matrix TensorProduct

namespace Formalism.HermitianLattices.Ext.L3.LITr

section Det

variable {R : Type*} [CommRing R] {m : ℕ}

end Det

section Herm

variable {K F : Type*} [Field K] [CharZero K] [StarRing K] [Field F] [Algebra F K] {m : ℕ}

def hermSub (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) K) where
  carrier := {B | Bᴴ = B}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, show aᴴ = a from ha, show bᴴ = b from hb]
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c B hB
    change (c • B)ᴴ = c • B
    rw [← algebraMap_smul K c B, Matrix.conjTranspose_smul, show Bᴴ = B from hB, (hF _).2 ⟨c, rfl⟩]

variable (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_hermSub (B : Matrix (Fin m) (Fin m) K) : B ∈ hermSub hF m ↔ Bᴴ = B := Iff.rfl

noncomputable def toMat (m : ℕ) : K ⊗[F] (hermSub hF m) →ₗ[K] Matrix (Fin m) (Fin m) K :=
  (hermSub hF m).subtype.liftBaseChange K

/- English proof (translation)
Simplify using `[toMat]`.
-/
theorem toMat_tmul (a : K) (B : hermSub hF m) :
    toMat hF m (a ⊗ₜ B) = a • (B : Matrix (Fin m) (Fin m) K) := by
  simp [toMat]

include hF in
/- English proof (translation)
Take `⟨x, hx⟩` from `(hF ((a + star a) / 2)).1 (by`. Rewrite using `[star_div₀, star_add, star_star, star_ofNat, add_comm])`. Take `⟨y, hy⟩` from `(hF ((a - star a) / (2 * δ))).1 (by`. Rewrite using `[star_div₀, star_sub, star_star, star_mul', star_ofNat, hδ]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Use `⟨x, y, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (a : K) :
    ∃ x y : F, a = algebraMap F K x + δ * algebraMap F K y := by
  obtain ⟨x, hx⟩ := (hF ((a + star a) / 2)).1 (by
    rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
  obtain ⟨y, hy⟩ := (hF ((a - star a) / (2 * δ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hδ]
    field_simp
    ring)
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  field_simp
  ring

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul a B`. Take `⟨x, y, rfl⟩` from `exists_decomp hF hδ hδ0 a`. Use `⟨x • B, y • B, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm δ]`. Consider the case `add s t hs ht`. Take `⟨B, C, rfl⟩` from `hs`. Take `⟨B', C', rfl⟩` from `ht`. Use `⟨B + B', C + C', ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_add, TensorProduct.tmul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_tensor_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (t : K ⊗[F] (hermSub hF m)) :
    ∃ B C : hermSub hF m, t = (1 : K) ⊗ₜ B + δ ⊗ₜ C := by
  induction t with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a B =>
    obtain ⟨x, y, rfl⟩ := exists_decomp hF hδ hδ0 a
    refine ⟨x • B, y • B, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_comm δ]
  | add s t hs ht =>
    obtain ⟨B, C, rfl⟩ := hs
    obtain ⟨B', C', rfl⟩ := ht
    refine ⟨B + B', C + C', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Take `⟨B, C, rfl⟩` from `exists_tensor_decomp hF hδ hδ0 t`. Rewrite `ht` using `[map_add, toMat_tmul, toMat_tmul, one_smul]`. Establish `ht'` using `congrArg Matrix.conjTranspose ht`.

Rewrite `ht'` using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (mem_hermSub hF _).1 B.2, (mem_hermSub hF _).1 C.2, hδ, Matrix.conjTranspose_zero, neg_smul]`. Establish `hB : (B : Matrix (Fin m) (Fin m) K) = 0`. Establish `: (2 : K) • (B : Matrix (Fin m) (Fin m) K) = 0`. Rewrite using `[two_smul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(smul_eq_zero.1 this).resolve_left two_ne_zero`. Establish `hC : (C : Matrix (Fin m) (Fin m) K) = 0`. Rewrite `ht` using `[hB, zero_add]`. Conclude with `(smul_eq_zero.1 ht).resolve_left hδ0`. Rewrite using `[Subtype.ext (a1 := B) (a2 := 0) hB, Subtype.ext (a1 := C) (a2 := 0) hC]`.

Simplify using the standard rewrite rules.
-/
theorem toMat_injective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Injective (toMat hF m) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨B, C, rfl⟩ := exists_tensor_decomp hF hδ hδ0 t
  rw [map_add, toMat_tmul, toMat_tmul, one_smul] at ht
  have ht' := congrArg Matrix.conjTranspose ht
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (mem_hermSub hF _).1 B.2,
    (mem_hermSub hF _).1 C.2, hδ, Matrix.conjTranspose_zero, neg_smul] at ht'
  have hB : (B : Matrix (Fin m) (Fin m) K) = 0 := by
    have : (2 : K) • (B : Matrix (Fin m) (Fin m) K) = 0 := by
      rw [two_smul]
      calc _ = ((B : Matrix (Fin m) (Fin m) K) + δ • (C : Matrix (Fin m) (Fin m) K)) +
            ((B : Matrix (Fin m) (Fin m) K) + -(δ • (C : Matrix (Fin m) (Fin m) K))) := by abel
        _ = 0 := by rw [ht, ht', add_zero]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hC : (C : Matrix (Fin m) (Fin m) K) = 0 := by
    rw [hB, zero_add] at ht
    exact (smul_eq_zero.1 ht).resolve_left hδ0
  rw [Subtype.ext (a1 := B) (a2 := 0) hB, Subtype.ext (a1 := C) (a2 := 0) hC]
  simp

/- English proof (translation)
Introduce `X`. Establish `h1 : ((2 : K)⁻¹ • (X + Xᴴ)) ∈ hermSub hF m`. Rewrite using `[mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, star_inv₀, star_ofNat, add_comm]`. Establish `h2 : ((2 * δ)⁻¹ • (X - Xᴴ)) ∈ hermSub hF m`. Rewrite using `[mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul', star_ofNat, hδ, mul_neg, inv_neg, neg_smul, ← smul_neg, neg_sub]`.

Use `⟨(1 : K) ⊗ₜ ⟨_, h1⟩ + δ ⊗ₜ ⟨_, h2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, toMat_tmul, toMat_tmul, one_smul, smul_smul]`. Establish `: δ * (2 * δ)⁻¹ = (2 : K)⁻¹` using `by field_simp`. Rewrite using `[this, ← smul_add]`. Establish `: X + Xᴴ + (X - Xᴴ) = (2 : K) • X` using `by rw [two_smul]; abel`.

Rewrite using `[this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]`.
-/
theorem toMat_surjective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Surjective (toMat hF m) := by
  intro X
  have h1 : ((2 : K)⁻¹ • (X + Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_ofNat, add_comm]
  have h2 : ((2 * δ)⁻¹ • (X - Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul', star_ofNat, hδ, mul_neg, inv_neg,
      neg_smul, ← smul_neg, neg_sub]
  refine ⟨(1 : K) ⊗ₜ ⟨_, h1⟩ + δ ⊗ₜ ⟨_, h2⟩, ?_⟩
  rw [map_add, toMat_tmul, toMat_tmul, one_smul, smul_smul]
  have : δ * (2 * δ)⁻¹ = (2 : K)⁻¹ := by field_simp
  rw [this, ← smul_add]
  have : X + Xᴴ + (X - Xᴴ) = (2 : K) • X := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

noncomputable def toMatEquiv {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (m : ℕ) :
    K ⊗[F] (hermSub hF m) ≃ₗ[K] Matrix (Fin m) (Fin m) K :=
  LinearEquiv.ofBijective (toMat hF m) ⟨toMat_injective hF hδ hδ0, toMat_surjective hF hδ hδ0⟩

def conjHerm (P : Matrix (Fin m) (Fin m) K) : hermSub hF m →ₗ[F] hermSub hF m where
  toFun B := ⟨Pᴴ * (B : Matrix (Fin m) (Fin m) K) * P, by
    rw [mem_hermSub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (mem_hermSub hF _).1 B.2, Matrix.mul_assoc]⟩
  map_add' B C := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    apply Subtype.ext
    simp

end Herm

end Formalism.HermitianLattices.Ext.L3.LITr
