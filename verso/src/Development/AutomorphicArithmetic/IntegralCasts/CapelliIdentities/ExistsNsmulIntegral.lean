import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Establish `h2 : IsIntegral ℤ (y • (y • a))` using `hint.smul y`. Use `⟨(y * y).natAbs, Int.natAbs_ne_zero.mpr (mul_ne_zero hy hy), ⟨y • (y • a), h2⟩, ?_⟩` and prove the remaining obligations. Establish `h3 : (((y * y).natAbs : ℕ) : E) = ((y * y : ℤ) : E)`.

Rewrite using `[← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]`. Rewrite using `[h3]`. Express the relevant statement in the definitionally equal form `y • (y • a) = _`. Rewrite using `[smul_smul, zsmul_eq_mul]`.
-/
private theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ M : ℕ, M ≠ 0 ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (M : E) * a := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • (y • a)) := hint.smul y
  refine ⟨(y * y).natAbs, Int.natAbs_ne_zero.mpr (mul_ne_zero hy hy), ⟨y • (y • a), h2⟩, ?_⟩
  have h3 : (((y * y).natAbs : ℕ) : E) = ((y * y : ℤ) : E) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [h3]
  change y • (y • a) = _
  rw [smul_smul, zsmul_eq_mul]

/- English proof (translation)
Introduce `E _ _ _ r X u`. Establish `hu : u ∈ Submodule.span E (X.Λ : Set (Fin r → E))`. Rewrite using `[X.Λ_span]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact X.Λ.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨M, hM, hx⟩` from `hx`. Take `⟨N, hN, hy⟩` from `hy`.

Use `⟨M * N, mul_ne_zero hM hN, ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_add]`. Use `X.Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hx N`.

Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hy M`. Consider the case `smul a x _ hx`. Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, b, hb⟩` from `UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral a`.

Use `⟨M * N, mul_ne_zero hM hN, ?_⟩` and prove the remaining obligations. Establish `h : (M * N) • a • x = b • (N • x)`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(M * N) • (a * x i) = (b : E) * (N • x i)`. Rewrite using `[hb, nsmul_eq_mul, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `X.Λ.smul_mem b hx`.
-/
theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → E), ∃ (N : ℕ), N ≠ (0 : ℕ) ∧ N • u ∈ X.Λ := by
  intro E _ _ _ r X u
  have hu : u ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [nsmul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx N
    · rw [mul_smul]; exact nsmul_mem hy M
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, b, hb⟩ := UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral a
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : (M * N) • a • x = b • (N • x) := by
      funext i
      change (M * N) • (a * x i) = (b : E) * (N • x i)
      rw [hb, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [h]
    exact X.Λ.smul_mem b hx
