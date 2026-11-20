import Mathlib

namespace GlobalTheory.SmulMemComapLattice

open NumberField

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (L : Set V)` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ hax`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hby`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := R) c`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hqK : algebraMap R K q ≠ 0`. Simplify using `using hq0`.

Use `⟨q * a, mul_ne_zero hq0 ha, ?_⟩` and prove the remaining obligations. Establish `: (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x`. Rewrite using `[← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `L.smul_mem _ hax`.
-/
theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hax
    · rw [mul_smul]; exact L.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap R K q ≠ 0 := by
      simpa using hq0
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have : (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x := by
      rw [← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hax

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype)` using `W.injective_subtype`. Use `Submodule.fg_of_fg_map_injective _ hinj ?_` and prove the remaining obligations. Conclude with `Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)`. Rewrite using `[eq_top_iff]`.

Introduce `w _`. Take `⟨a, ha, haw⟩` from `exists_smul_mem Λ hΛ.span_eq_top (w : V)`. Establish `haK : algebraMap (𝓞 K) K a ≠ 0` using `by simpa using ha`. Establish `hw : w = (algebraMap (𝓞 K) K a)⁻¹ • (a • w)`. Rewrite using `[← algebraMap_smul K a w, smul_smul, inv_mul_cancel₀ haK, one_smul]`.

Rewrite using `[hw]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using `using haw`.
-/
theorem isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro w _
    obtain ⟨a, ha, haw⟩ := exists_smul_mem Λ hΛ.span_eq_top (w : V)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hw : w = (algebraMap (𝓞 K) K a)⁻¹ • (a • w) := by
      rw [← algebraMap_smul K a w, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [hw]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simpa using haw

end GlobalTheory.SmulMemComapLattice
