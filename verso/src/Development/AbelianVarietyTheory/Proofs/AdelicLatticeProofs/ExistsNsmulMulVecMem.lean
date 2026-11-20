import Mathlib

namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

/- English proof (translation)
Establish `h : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨y, hy, hint⟩` from `h.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Rewrite `hint` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with h1 | h1` into its components or cases.

Establish `: ((y.natAbs : ℕ) : E) = (y : E)` using `by conv_rhs => rw [h1]`. Conclude with `(Int.cast_natCast _).symm`. Rewrite using `[this]`. Conclude with `hint`. Establish `: ((y.natAbs : ℕ) : E) = -(y : E)` using `by conv_rhs => rw [h1]`.

Rewrite using `[Int.cast_neg, neg_neg]`. Conclude with `(Int.cast_natCast _).symm`. Rewrite using `[this, neg_mul]`. Conclude with `hint.neg`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (↑L : Set (Fin n → E))` using `by rw [hL]; trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hxa⟩` from `hx`. Take `⟨b, hb, hyb⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hxa b`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hyb a`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hxa⟩` from `hx`. Take `⟨K, hK, hint⟩` from `exists_nat_mul_integral c`. Use `⟨K * a, Nat.mul_pos hK ha, ?_⟩` and prove the remaining obligations. Establish `h` using `L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Express the relevant statement in the definitionally equal form `_ = ((K : E) * c) * (a • x i)`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (↑L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨K, hK, hint⟩ := exists_nat_mul_integral c
    refine ⟨K * a, Nat.mul_pos hK ha, ?_⟩
    have h := L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa
    convert h using 1
    ext i
    change _ = ((K : E) * c) * (a • x i)
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

/- English proof (translation)
Take `⟨s, hs⟩` from `hfg`. Use `choose f hf0 hf using exists_nsmul_mem L hL`. Use `⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv` using `[← hs]`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)`. Rewrite using `[hk, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hf _) k`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add, smul_add]`. Conclude with `L.add_mem hx hy`. Consider the case `smul c x _ hx`.

Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Conclude with `L.smul_mem c hx`.
-/
theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
