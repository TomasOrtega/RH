import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CompanionTheory.HatBound

/- English proof (translation)
Establish `hx : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨y, hy, h⟩` from `hx.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq y with h1 | h1` into its components or cases. Use `⟨⟨y • x, h⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y • x = _`. Rewrite using `[zsmul_eq_mul]`. Use `congr 1`. Use `conv_lhs => rw [h1]`. Simplify using `only [Int.cast_natCast]`.

Use `⟨⟨-(y • x), h.neg⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(y • x) = _`. Rewrite using `[zsmul_eq_mul, ← neg_mul]`. Use `congr 1`. Use `conv_lhs => rw [h1]`.

Simplify using `only [Int.cast_neg, Int.cast_natCast, neg_neg]`.
-/
theorem exists_nat_mul_integer (K : Type) [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 K, (r : K) = m * x := by
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, h⟩ := hx.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨⟨y • x, h⟩, ?_⟩
    change y • x = _
    rw [zsmul_eq_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_natCast]
  · refine ⟨⟨-(y • x), h.neg⟩, ?_⟩
    change -(y • x) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m, hm, hx⟩` from `hx`. Take `⟨m', hm', hy⟩` from `hy`. Use `⟨m * m', mul_pos hm hm', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hx _`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hy _`. Consider the case `smul c x _ hx`.

Take `⟨m, hm, hx⟩` from `hx`. Take `⟨m', hm', r, hr⟩` from `exists_nat_mul_integer E c`. Use `⟨m * m', mul_pos hm hm', ?_⟩` and prove the remaining obligations. Establish `: (m * m') • c • x = r • (m • x)`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(m * m') • (c * x i) = (r : E) * (m • x i)`. Rewrite using `[hr, nsmul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `L.smul_mem r hx`.
-/
theorem exists_nsmul_mem_lattice [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', hy⟩ := hy
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx _
    · rw [mul_smul]; exact nsmul_mem hy _
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', r, hr⟩ := exists_nat_mul_integer E c
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    have : (m * m') • c • x = r • (m • x) := by
      funext i
      change (m * m') • (c * x i) = (r : E) * (m • x i)
      rw [hr, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [this]
    exact L.smul_mem r hx

end GlobalTheory.CompanionTheory.HatBound
