import Mathlib

universe u_1 u_2

namespace GlobalTheory.IntegerScalarIntegral

open NumberField

/- English proof (translation)
Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)`. Conclude with `hc.exists_integral_multiple`.
-/
theorem exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple

/- English proof (translation)
Establish `hy : y ∈ Submodule.span K (L : Set V)` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem hax b`. Rewrite using `[mul_smul]`. Conclude with `zsmul_mem hbz a`. Consider the case `smul c x _ hx`.

Take `⟨m, hm, hmx⟩` from `hx`. Take `⟨d, hd, hint⟩` from `exists_int_smul_integral c`. Use `⟨d * m, mul_ne_zero hd hm, ?_⟩` and prove the remaining obligations. Set `r : 𝓞 K` to `⟨d • c, hint⟩`. Establish `hr : (algebraMap (𝓞 K) K r) = d • c` using `rfl`.

Establish `key : (d * m) • (c • x) = r • (m • x)`. Rewrite using `[← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]`. Rewrite using `[key]`. Conclude with `L.smul_mem r hmx`.
-/
theorem exists_int_smul_mem {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx

/- English proof (translation)
Introduce `L hL y` and use `exists_int_smul_mem L hL y`.
-/
theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y

end GlobalTheory.IntegerScalarIntegral
