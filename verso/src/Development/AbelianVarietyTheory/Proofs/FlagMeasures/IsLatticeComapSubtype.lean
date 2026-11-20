import Mathlib

namespace GlobalTheory.SmulMemComapLattice

open NumberField

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
