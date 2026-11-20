import Mathlib

namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

/- English proof (translation)
Break down `subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt` into its components or cases. Conclude with `⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩`. Establish `: ExpChar (TensorProduct k K B) q` using `expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul x b`. Take `⟨n, c, hc⟩` from `IsPurelyInseparable.pow_mem k q x`. Use `⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy`.

Take `⟨n1, h1⟩` from `hx`. Take `⟨n2, h2⟩` from `hy`. Use `⟨n1 + n2, ?_⟩` and prove the remaining obligations. Establish `e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2` using `by rw [pow_add, pow_mul]`. Establish `e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1` using `by rw [pow_add, mul_comm, pow_mul]`.

Rewrite using `[add_pow_expChar_pow, e1, e2]`. Conclude with `add_mem (pow_mem h1 _) (pow_mem h2 _)`.
-/
theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
