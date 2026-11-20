import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.IsomMulTorus

open GlobalTheory.UnitLemma

/- English proof (translation)
Establish `h` using `Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) w`. Rewrite using `[h, RingEquiv.apply_symm_apply]`.
-/
theorem trace_inv {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) w
  rw [h, RingEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `K B n u β hβ hadj hnd f hf hiso`. Establish `hsub : ∀ a b z : B.A, B.herm β (a - b) z = B.herm β a z - B.herm β b z`. Introduce `a b z`. Unfold `InvAlg.herm`. Rewrite using `[mul_sub, sub_mul, map_sub]`.

Establish `hsym : ∀ y z : B.A, K.c (B.herm β z y) = B.herm β (((-1) ^ n * u) * y) z`. Introduce `y z`. Unfold `InvAlg.herm`. Rewrite using `[← trace_inv, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `ht : ∀ y, f (((-1) ^ n * u) * y) = ((-1) ^ n * u) * f y`. Introduce `y`. Establish `h0 : ∀ z, B.herm β (((-1) ^ n * u) * f y - f (((-1) ^ n * u) * y)) z = 0`. Introduce `z`.

Take `⟨w, rfl⟩` from `hf z`. Rewrite using `[hsub, ← hsym, hiso, hiso, hsym, sub_self]`. Conclude with `(sub_eq_zero.mp (hnd _ h0)).symm`. Establish `hsgn : ((-1 : B.A) ^ n) = algebraMap K.E B.A ((-1) ^ n)` using `by simp`. Establish `hsq : ((-1 : B.A) ^ n) * (-1) ^ n = 1` using `by rw [← mul_pow]; simp`.

Establish `hu : ∀ y, f (u * y) = u * f y`. Introduce `y`. Establish `e1 : u * y = (-1) ^ n * (((-1) ^ n * u) * y)`. Rewrite using `[← mul_assoc, ← mul_assoc, hsq, one_mul]`. Establish `e2 : u * f y = (-1) ^ n * (((-1) ^ n * u) * f y)`.

Rewrite using `[← mul_assoc, ← mul_assoc, hsq, one_mul]`. Establish `hm : ∀ x, f ((-1) ^ n * x) = (-1) ^ n * f x`. Introduce `x`. Rewrite using `[hsgn, ← Algebra.smul_def, map_smul, Algebra.smul_def]`. Rewrite using `[e1, e2, hm, ht]`.

Set `S : Subalgebra K.E B.A` to `{ carrier := {x | ∀ y, f (x * y) = x * f y} mul_mem' := by`. Introduce `a b ha hb y`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[mul_assoc, ha, hb, mul_assoc]`. Use the proof step `add_mem' := by`.

Introduce `a b ha hb y`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[add_mul, map_add, ha, hb, add_mul]`. Use the proof step `algebraMap_mem' := by`. Introduce `e y`.

Use `show f (algebraMap K.E B.A e * y) = algebraMap K.E B.A e * f y`. Rewrite using `[← Algebra.smul_def, ← Algebra.smul_def, map_smul] }`. Establish `hS : ∀ x, ∀ y, f (x * y) = x * f y`. Introduce `x`. Establish `h1 : Algebra.adjoin K.E {u} ≤ S` using `Algebra.adjoin_le (by`.

Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `hu)`. Rewrite `h1` using `[hadj]`.

Conclude with `h1 (Algebra.mem_top : x ∈ (⊤ : Subalgebra K.E B.A))`. Establish `hf1 : ∀ y, f y = y * f 1`. Introduce `y`. Rewrite using `[← hS y 1, mul_one]`. Take `⟨z, hz⟩` from `hf 1`.

Establish `hz1 : f 1 * z = 1` using `by rw [mul_comm, ← hf1, hz]`. Set `a : B.Aˣ` to `⟨f 1, z, hz1, by rw [mul_comm]; exact hz1⟩`. Use `⟨a, ?_, fun y => by rw [hf1 y, mul_comm]⟩` and prove the remaining obligations. Use `show (f 1) * B.σ (f 1) = 1`. Establish `h0 : ∀ w, B.herm β (f 1 * B.σ (f 1) - 1) w = 0`.

Introduce `w`. Establish `e : B.herm β (f 1 * B.σ (f 1)) w = B.herm β (f 1) (f w)`. Rewrite using `[hf1 w]`. Unfold `InvAlg.herm`. Rewrite using `[map_mul B.σ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsub, e, hiso, sub_self]`. Conclude with `sub_eq_zero.mp (hnd _ h0)`.
-/
theorem isom_eq_mul : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (u β : B.A), B.σ β = β * ((-1) ^ n * u) → Algebra.adjoin K.E {u} = ⊤ → (∀ y, (∀ z, B.herm β y z = 0) → y = 0) → ∀ f : B.A →ₗ[K.E] B.A, Function.Surjective f → (∀ y z, B.herm β (f y) (f z) = B.herm β y z) → ∃ a : B.Aˣ, a ∈ B.T ∧ ∀ y, f y = (a : B.A) * y := by
  intro K B n u β hβ hadj hnd f hf hiso

  have hsub : ∀ a b z : B.A, B.herm β (a - b) z = B.herm β a z - B.herm β b z := by
    intro a b z; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]

  have hsym : ∀ y z : B.A, K.c (B.herm β z y) = B.herm β (((-1) ^ n * u) * y) z := by
    intro y z
    unfold InvAlg.herm
    rw [← trace_inv, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]
    congr 1; ring

  have ht : ∀ y, f (((-1) ^ n * u) * y) = ((-1) ^ n * u) * f y := by
    intro y
    have h0 : ∀ z, B.herm β (((-1) ^ n * u) * f y - f (((-1) ^ n * u) * y)) z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hf z
      rw [hsub, ← hsym, hiso, hiso, hsym, sub_self]
    exact (sub_eq_zero.mp (hnd _ h0)).symm

  have hsgn : ((-1 : B.A) ^ n) = algebraMap K.E B.A ((-1) ^ n) := by simp
  have hsq : ((-1 : B.A) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hu : ∀ y, f (u * y) = u * f y := by
    intro y
    have e1 : u * y = (-1) ^ n * (((-1) ^ n * u) * y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have e2 : u * f y = (-1) ^ n * (((-1) ^ n * u) * f y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have hm : ∀ x, f ((-1) ^ n * x) = (-1) ^ n * f x := by
      intro x; rw [hsgn, ← Algebra.smul_def, map_smul, Algebra.smul_def]
    rw [e1, e2, hm, ht]

  let S : Subalgebra K.E B.A :=
    { carrier := {x | ∀ y, f (x * y) = x * f y}
      mul_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_assoc, ha, hb, mul_assoc]
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_mul, map_add, ha, hb, add_mul]
      algebraMap_mem' := by
        intro e y
        show f (algebraMap K.E B.A e * y) = algebraMap K.E B.A e * f y
        rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul] }
  have hS : ∀ x, ∀ y, f (x * y) = x * f y := by
    intro x
    have h1 : Algebra.adjoin K.E {u} ≤ S := Algebra.adjoin_le (by
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hu)
    rw [hadj] at h1
    exact h1 (Algebra.mem_top : x ∈ (⊤ : Subalgebra K.E B.A))
  have hf1 : ∀ y, f y = y * f 1 := by
    intro y; rw [← hS y 1, mul_one]
  obtain ⟨z, hz⟩ := hf 1
  have hz1 : f 1 * z = 1 := by rw [mul_comm, ← hf1, hz]
  let a : B.Aˣ := ⟨f 1, z, hz1, by rw [mul_comm]; exact hz1⟩
  refine ⟨a, ?_, fun y => by rw [hf1 y, mul_comm]⟩
  show (f 1) * B.σ (f 1) = 1
  have h0 : ∀ w, B.herm β (f 1 * B.σ (f 1) - 1) w = 0 := by
    intro w
    have e : B.herm β (f 1 * B.σ (f 1)) w = B.herm β (f 1) (f w) := by
      rw [hf1 w]; unfold InvAlg.herm; rw [map_mul B.σ]; congr 1; ring
    rw [hsub, e, hiso, sub_self]
  exact sub_eq_zero.mp (hnd _ h0)

end GlobalTheory.IsomMulTorus
