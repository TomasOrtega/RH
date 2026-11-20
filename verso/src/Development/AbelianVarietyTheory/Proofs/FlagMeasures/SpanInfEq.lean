import Mathlib

namespace GlobalTheory.SpanInfEq

open NumberField

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (L : Set V)` using `by rw [hL.span_eq_top]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d₁, hd₁, h₁⟩` from `hx`. Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ h₂`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, h⟩` from `hx`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := RingOfIntegers K) c`. Use `⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩` and prove the remaining obligations. Establish `hb' : algebraMap (RingOfIntegers K) K b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `: (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x) = a • (d • x)`.

Rewrite using `[← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `L.smul_mem _ h`.
-/
theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `(Submodule.mem_inf.mp hx).2`. Introduce `v hv`.

Take `⟨d, hd, h⟩` from `exists_smul_mem L hL v`. Establish `hd' : algebraMap (RingOfIntegers K) K d ≠ 0`. Introduce `h0`. Conclude with `hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)`. Establish `hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T`.

Rewrite using `[← algebraMap_smul K d v]`. Conclude with `T.smul_mem _ hv`. Establish `hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T` using `Submodule.mem_inf.mpr ⟨h, hdT⟩`. Establish `: v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v)`. Rewrite using `[← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Introduce `L hL T` and use `span_inf_eq L hL T`.
-/
theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T :=
  fun L hL T => span_inf_eq L hL T

end GlobalTheory.SpanInfEq
