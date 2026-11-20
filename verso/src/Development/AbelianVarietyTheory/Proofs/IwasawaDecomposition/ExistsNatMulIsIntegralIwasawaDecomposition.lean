import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ (L := E) {c}`. Establish `hc` using `h c (Finset.mem_singleton_self c)`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg y`. Use `⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩` and prove the remaining obligations. Establish `: ((n : ℕ) : E) * c = ((n : ℤ)) • c` using `by rw [zsmul_eq_mul]; push_cast; rfl`.

Rewrite using `[this]`. Conclude with `hc`. Use `⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩` and prove the remaining obligations. Establish `: ((n : ℕ) : E) * c = -((-(n : ℤ)) • c)` using `by rw [zsmul_eq_mul]; push_cast; ring`. Rewrite using `[this]`.

Conclude with `hc.neg`.
-/
theorem exists_nat_mul_isIntegral_iwasawa_decomposition (E : Type) [Field E] [NumberField E] (c : E) :
    ∃ a : ℕ, 0 < a ∧ IsIntegral ℤ ((a : E) * c) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) {c}
  have hc := h c (Finset.mem_singleton_self c)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = ((n : ℤ)) • c := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hc
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hc.neg

/- English proof (translation)
Introduce `E _ _ _ N X v`. Establish `hv : v ∈ Submodule.span E (X.Λ : Set (Fin N → E))` using `by rw [X.Λ_span]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨d1, hd1, h1⟩` from `hx`. Take `⟨d2, hd2, h2⟩` from `hy`. Use `⟨d1 * d2, Nat.mul_pos hd1 hd2, ?_⟩` and prove the remaining obligations. Establish `e : ((d1 * d2 : ℕ) : E) • (x + y) = d2 • ((d1 : E) • x) + d1 • ((d2 : E) • y)`.

Simplify using `only [← Nat.cast_smul_eq_nsmul E, smul_smul, smul_add]`. Apply the tactic sequence `push_cast; congr 1 <;> congr 1 <;> ring`. Rewrite using `[e]`. Conclude with `X.Λ.add_mem (X.Λ.nsmul_mem h1 _) (X.Λ.nsmul_mem h2 _)`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, h⟩` from `hx`. Take `⟨a, ha, hi⟩` from `exists_nat_mul_isIntegral_iwasawa_decomposition E c`. Use `⟨a * d, Nat.mul_pos ha hd, ?_⟩` and prove the remaining obligations. Set `k : 𝓞 E` to `⟨(a : E) * c, hi⟩`. Establish `e : ((a * d : ℕ) : E) • (c • x) = k • ((d : E) • x)`.

Rewrite using `[← algebraMap_smul E k ((d : E) • x), smul_smul, smul_smul]`. Use `show _ = (((a : E) * c) * (d : E)) • x`. Use `push_cast`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `X.Λ.smul_mem k h`.
-/
theorem exists_nat_smul_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (v : Fin N → E), ∃ d : ℕ, 0 < d ∧ (d : E) • v ∈ X.Λ := by
  intro E _ _ _ N X v
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ?_⟩
    have e : ((d1 * d2 : ℕ) : E) • (x + y) = d2 • ((d1 : E) • x) + d1 • ((d2 : E) • y) := by
      simp only [← Nat.cast_smul_eq_nsmul E, smul_smul, smul_add]
      push_cast; congr 1 <;> congr 1 <;> ring
    rw [e]
    exact X.Λ.add_mem (X.Λ.nsmul_mem h1 _) (X.Λ.nsmul_mem h2 _)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, ha, hi⟩ := exists_nat_mul_isIntegral_iwasawa_decomposition E c
    refine ⟨a * d, Nat.mul_pos ha hd, ?_⟩
    let k : 𝓞 E := ⟨(a : E) * c, hi⟩
    have e : ((a * d : ℕ) : E) • (c • x) = k • ((d : E) • x) := by
      rw [← algebraMap_smul E k ((d : E) • x), smul_smul, smul_smul]
      show _ = (((a : E) * c) * (d : E)) • x
      push_cast; congr 1; ring
    rw [e]
    exact X.Λ.smul_mem k h

end GlobalTheory.UnipKill
