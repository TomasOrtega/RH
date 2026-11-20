import Mathlib

namespace GlobalTheory.NatMulIntegral

open NumberField

/- English proof (translation)
Establish `h1 : IsAlgebraic ℚ a` using `Algebra.IsAlgebraic.isAlgebraic a`. Establish `h2 : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1`. Take `⟨y, hy, hi⟩` from `h2.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩` and prove the remaining obligations. Rewrite `hi` using `[zsmul_eq_mul]`.

Establish `hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E)` using `(Int.cast_natCast _).symm`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite using `[hc, ← h]`. Conclude with `hi`. Establish `h' : (y.natAbs : ℤ) = -y` using `by omega`.

Rewrite using `[hc, h', Int.cast_neg, neg_mul]`. Conclude with `hi.neg`.
-/
theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hx d`.
-/
theorem nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d

/- English proof (translation)
Establish `hy : y ∈ Submodule.span E (L : Set (Fin n → E))` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨d, hd, hdx⟩` from `hx`. Take `⟨e, he, hez⟩` from `hz`. Use `⟨d * e, Nat.mul_pos hd he, ?_⟩` and prove the remaining obligations. Establish `h1` using `nat_smul_mem L e hdx`. Establish `h2` using `nat_smul_mem L d hez`.

Establish `: ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z`. Rewrite using `[smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]`. Rewrite using `[this]`. Conclude with `L.add_mem h1 h2`. Consider the case `smul a x _ hx`.

Take `⟨d, hd, hdx⟩` from `hx`. Take `⟨e, he, hea⟩` from `exists_nat_mul_isIntegral a`. Use `⟨d * e, Nat.mul_pos hd he, ?_⟩` and prove the remaining obligations. Set `b : RingOfIntegers E` to `⟨(e : E) * a, hea⟩`. Establish `h1 : b • (d : E) • x ∈ L` using `L.smul_mem b hdx`.

Establish `: ((d * e : ℕ) : E) • a • x = b • (d : E) • x`. Rewrite using `[← algebraMap_smul E b]`. Express the relevant statement in the definitionally equal form `_ = ((e : E) * a) • (d : E) • x`. Rewrite using `[smul_smul, smul_smul, Nat.cast_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `h1`.
-/
theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hez⟩ := hz
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have h1 := nat_smul_mem L e hdx
    have h2 := nat_smul_mem L d hez
    have : ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]
    rw [this]
    exact L.add_mem h1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hea⟩ := exists_nat_mul_isIntegral a
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    let b : RingOfIntegers E := ⟨(e : E) * a, hea⟩
    have h1 : b • (d : E) • x ∈ L := L.smul_mem b hdx
    have : ((d * e : ℕ) : E) • a • x = b • (d : E) • x := by
      rw [← algebraMap_smul E b]
      change _ = ((e : E) * a) • (d : E) • x
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact h1

end GlobalTheory.NatMulIntegral
