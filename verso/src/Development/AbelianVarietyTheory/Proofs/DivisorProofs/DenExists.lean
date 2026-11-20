import Mathlib

namespace GlobalTheory.DenominatorExistence

open NumberField

/- English proof (translation)
Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨y, hy, hint⟩` from `hc.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `h' : (y.natAbs : ℤ) = y` using `by omega`.

Establish `h2 : ((y.natAbs : ℤ) : E) = (y : E)` using `congrArg _ h'`. Rewrite `h2` using `[Int.cast_natCast]`. Rewrite using `[h2, ← zsmul_eq_mul]`. Conclude with `hint`. Establish `h' : (y.natAbs : ℤ) = -y` using `by omega`.

Establish `h2 : ((y.natAbs : ℤ) : E) = ((-y : ℤ) : E)` using `congrArg _ h'`. Rewrite `h2` using `[Int.cast_natCast, Int.cast_neg]`. Rewrite using `[h2, neg_mul, ← zsmul_eq_mul]`. Conclude with `hint.neg`.
-/
theorem den_exists {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := hc.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have h' : (y.natAbs : ℤ) = y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = (y : E) := congrArg _ h'
    rw [Int.cast_natCast] at h2
    rw [h2, ← zsmul_eq_mul]; exact hint
  · have h' : (y.natAbs : ℤ) = -y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = ((-y : ℤ) : E) := congrArg _ h'
    rw [Int.cast_natCast, Int.cast_neg] at h2
    rw [h2, neg_mul, ← zsmul_eq_mul]; exact hint.neg

/- English proof (translation)
Establish `key : ∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ n • v ∈ Λ`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))` using `by rw [hspan]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_nsmul]`. Conclude with `Λ.toAddSubmonoid.nsmul_mem hax b`. Rewrite using `[mul_comm, mul_nsmul]`.

Conclude with `Λ.toAddSubmonoid.nsmul_mem hby a`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨d, hd, hdc⟩` from `den_exists c`. Use `⟨d * a, Nat.mul_pos hd ha, ?_⟩` and prove the remaining obligations.

Establish `e1 : (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x) = ((d : E) * c) • (a • x)`. Rewrite using `[← algebraMap_smul E]`. Both sides reduce to the same expression. Establish `e : (d * a) • (c • x) = (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x)`. Rewrite using `[e1, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Λ.smul_mem _ hax`.

Take `⟨s, hs⟩` from `hfg`. Use `choose f hfpos hfmem using key`. Use `⟨∏ x ∈ s, f x, Finset.prod_pos (fun x _ => hfpos x), ?_⟩` and prove the remaining obligations. Introduce `v hv`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Rewrite `hv` using `[← hs]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← Finset.mul_prod_erase s f hx, mul_nsmul]`. Conclude with `Λ.toAddSubmonoid.nsmul_mem (hfmem x) _`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Λ.add_mem hx hy`. Consider the case `smul o x _ hx => rw [smul_comm]`. Conclude with `Λ.smul_mem o hx`.
-/
theorem main {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ Λ' : Submodule (RingOfIntegers E) (Fin r → E)) (hfg : Λ'.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by

  have key : ∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ n • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      rw [smul_add]
      refine Λ.add_mem ?_ ?_
      · rw [mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hax b
      · rw [mul_comm, mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hby a
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨d, hd, hdc⟩ := den_exists c
      refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
      have e1 : (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x)
          = ((d : E) * c) • (a • x) := by
        rw [← algebraMap_smul E]; rfl
      have e : (d * a) • (c • x) = (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x) := by
        rw [e1, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]
        congr 1
        push_cast; ring
      rw [e]; exact Λ.smul_mem _ hax
  obtain ⟨s, hs⟩ := hfg
  classical
  choose f hfpos hfmem using key
  refine ⟨∏ x ∈ s, f x, Finset.prod_pos (fun x _ => hfpos x), ?_⟩
  intro v hv
  rw [Nat.cast_smul_eq_nsmul]
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s f hx, mul_nsmul]
    exact Λ.toAddSubmonoid.nsmul_mem (hfmem x) _
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

end GlobalTheory.DenominatorExistence
