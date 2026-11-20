import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.UnipotentAdelicQuotients.ThmBInHecke

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralAdeleProducts

/- English proof (translation)
Introduce `v` and use `mul_mem (ha v) (hb v)`.
-/
theorem intAf_mul {F : Type} [Field F] [NumberField F] {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) (hb : b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) : a * b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F :=
  fun v => mul_mem (ha v) (hb v)

/- English proof (translation)
Unfold `HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht`. Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [neg_mul]`. Conclude with `neg_mem hx`. Consider the case `mem x hx`. Take `⟨a, ha, p, rfl⟩` from `hx`.

Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`. Consider the case `mem y hy`. Take `⟨b, hb, q, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression.
-/
theorem intAE_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) :
    s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  unfold HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht
  induction hs using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    obtain ⟨a, ha, p, rfl⟩ := hx
    induction ht using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨b, hb, q, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

end GlobalTheory.IntegralAdeleProducts
