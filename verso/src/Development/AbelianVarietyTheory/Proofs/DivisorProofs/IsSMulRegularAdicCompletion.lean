import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector

namespace GlobalTheory

/- English proof (translation)
Use `set I : Ideal A := Ideal.span {(p : A)}`. Introduce `x y hxy`. Establish `key : ∀ z : AdicCompletion I A, (p : AdicCompletion I A) * z = 0 → z = 0`. Introduce `z hz`. Apply `AdicCompletion.ext` to reduce the goal to its premises.

Introduce `n`. Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (z.val (n + 1))`. Establish `hz' : (p • z).val (n + 1) = 0`. Rewrite using `[nsmul_eq_mul, hz]`. Both sides reduce to the same expression.

Rewrite `hz'` using `[AdicCompletion.val_smul_apply, ← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `hmem : (p : A) * a ∈ Ideal.span {(p : A) ^ (n + 1)}`. Establish `: p • a = (p : A) * a` using `by rw [nsmul_eq_mul]`. Rewrite using `[← this, ← Ideal.span_singleton_pow]`. Simplify `hz'` using `[smul_eq_mul, Ideal.mul_top]`.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hab : a = (p : A) ^ n * b`. Apply `hp` to reduce the goal to its premises. Simplify using `only [smul_eq_mul]`. Rewrite using `[← hb]`.

Expand and normalize the polynomial expressions, which then agree. Establish `htr` using `z.property (Nat.le_succ n)`. Express the relevant statement in the definitionally equal form `AdicCompletion.transitionMap I A (Nat.le_succ n) (z.val (n + 1)) = z.val n at htr`. Rewrite using `[← htr, ← ha, AdicCompletion.val_zero_apply]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk a : A ⧸ (I ^ n • ⊤ : Submodule A A)) = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero, hab]`. Simplify using `only [smul_eq_mul, Ideal.mul_top, I, Ideal.span_singleton_pow]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩`. Establish `h0 : (p : AdicCompletion I A) * (x - y) = 0`. Rewrite using `[mul_sub, sub_eq_zero]`.

Conclude with `hxy`. Conclude with `sub_eq_zero.mp (key _ h0)`.
-/
theorem isSMulRegular_natCast_adicCompletion (p : ℕ) (A : Type) [CommRing A]
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A)
      (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  set I : Ideal A := Ideal.span {(p : A)}
  intro x y hxy
  have key : ∀ z : AdicCompletion I A, (p : AdicCompletion I A) * z = 0 → z = 0 := by
    intro z hz
    apply AdicCompletion.ext
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (z.val (n + 1))
    have hz' : (p • z).val (n + 1) = 0 := by
      rw [nsmul_eq_mul, hz]; rfl
    rw [AdicCompletion.val_smul_apply, ← ha, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hz'
    have hmem : (p : A) * a ∈ Ideal.span {(p : A) ^ (n + 1)} := by
      have : p • a = (p : A) * a := by rw [nsmul_eq_mul]
      rw [← this, ← Ideal.span_singleton_pow]
      simpa [smul_eq_mul, Ideal.mul_top] using hz'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    have hab : a = (p : A) ^ n * b := by
      apply hp
      simp only [smul_eq_mul]
      rw [← hb]; ring
    have htr := z.property (Nat.le_succ n)
    change AdicCompletion.transitionMap I A (Nat.le_succ n) (z.val (n + 1)) = z.val n at htr
    rw [← htr, ← ha, AdicCompletion.val_zero_apply]
    change (Submodule.Quotient.mk a : A ⧸ (I ^ n • ⊤ : Submodule A A)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hab]
    simp only [smul_eq_mul, Ideal.mul_top, I, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩
  have h0 : (p : AdicCompletion I A) * (x - y) = 0 := by
    rw [mul_sub, sub_eq_zero]; exact hxy
  exact sub_eq_zero.mp (key _ h0)

end GlobalTheory
