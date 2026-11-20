import Mathlib

namespace GlobalTheory.AlgebraMapToZMod

/- English proof (translation)
Use `haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩`. Establish `h` using `PadicInt.toZMod_spec x`. Rewrite `h` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `h`. Use `set z : ZMod l := PadicInt.toZMod x with hz`.

Establish `hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l])` using `(ZMod.natCast_val z).symm`. Establish `hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l])`. Rewrite using `[hy, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : f x = ((z.val : ℕ) : R)` using `by conv_lhs => rw [hx]`.

Rewrite using `[map_add, map_mul, hf, mul_zero, zero_add, map_natCast]`. Establish `h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R)` using `by conv_lhs => rw [← ZMod.natCast_zmod_val z]`. Rewrite using `[map_natCast]`. Rewrite using `[h1, h2]`.
-/
theorem algebraMap_toZMod_eq {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type} [inst_1 : Field R]
    [inst_2 : Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  set z : ZMod l := PadicInt.toZMod x with hz
  have hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l]) := (ZMod.natCast_val z).symm
  have hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l]) := by
    rw [hy, hc]; ring
  have h1 : f x = ((z.val : ℕ) : R) := by
    conv_lhs => rw [hx]
    rw [map_add, map_mul, hf, mul_zero, zero_add, map_natCast]
  have h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, h2]

end GlobalTheory.AlgebraMapToZMod
