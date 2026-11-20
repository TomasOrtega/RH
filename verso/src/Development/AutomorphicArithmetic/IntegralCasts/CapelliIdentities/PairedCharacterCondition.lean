import Mathlib

noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ M hM f`. Establish `key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M`. Introduce `c hc x hx`. Take `⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c` from `⟨⟨c, hc⟩, rfl⟩`. Rewrite using `[algebraMap_smul]`.

Conclude with `M.smul_mem r hx`. Establish `hint : ∀ n : ℤ, IsIntegral ℤ (n : K)` using `fun n => isIntegral_algebraMap (R := ℤ) (x := n)`. Establish `hf : f ∈ Submodule.span K (↑M : Set V)` using `hM ▸ Submodule.mem_top`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Establish `e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]`. Rewrite using `[e]`. Conclude with `M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hx⟩` from `hx`. Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨b, hb, hc⟩` from `halg.exists_integral_multiple`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x)`.

Rewrite using `[smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `key _ hc _ hx`.
-/
theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]
    rw [e]
    exact M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x) := by
      rw [smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]
      congr 1
      ring
    rw [e]
    exact key _ hc _ hx
