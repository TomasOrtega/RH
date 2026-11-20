import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPowMemRangeIncludeRight
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight`. Consider the case `exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight`. Consider the case `(apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)`.
-/
theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

/- English proof (translation)
Establish `hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B)` using `Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective`. Take `⟨n, b, hb⟩` from `pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e`. Establish `hpos : ringExpChar k ^ n ≠ 0` using `(pow_pos (expChar_pos k _) n).ne'`. Establish `h1 : e ^ (ringExpChar k ^ n) = e`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero hpos`.

Rewrite using `[hm]`. Conclude with `he.pow_succ_eq m`. Rewrite `hb` using `[h1]`. Establish `hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e` using `hb`. Establish `hbi : b * b = b`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hb']`. Conclude with `he`. Break down `isUnit_or_isUnit_one_sub_self b with hu | hu` into its components or cases. Use `right`.

Establish `: b = 1` using `hu.mul_left_cancel (by rw [hbi, mul_one])`. Rewrite using `[← hb', this, map_one]`. Use `left`. Establish `: b = 0` using `hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])`. Rewrite using `[← hb', this, map_zero]`.
-/
theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
