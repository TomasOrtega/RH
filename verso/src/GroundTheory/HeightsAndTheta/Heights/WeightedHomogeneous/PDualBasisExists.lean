import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

/- English proof (translation)
Take `⟨s, hs⟩` from `F.fg`. Set `ev : (Fin (r + 1) → K) →ₗ[ℤ] (s → K)` to `{ toFun := fun φ v ↦ φ ⬝ᵥ (v : Fin (r + 1) → K) map_add' := by`. Introduce `φ ψ`. Use function extensionality and compare the values at `v`. Simplify using `[add_dotProduct]`.

Use the proof step `map_smul' := by`. Introduce `c φ`. Use function extensionality and compare the values at `v`. Conclude with `smul_dotProduct c φ (v : Fin (r + 1) → K) }`. Establish `hspan : Submodule.span K (s : Set (Fin (r + 1) → K)) = ⊤`.

Rewrite using `[← Submodule.span_span_of_tower (R := 𝓞 K), hs, F.span_eq]`. Establish `hinj : Function.Injective ev`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `φ hφ`. Establish `h0 : ∀ w ∈ Submodule.span K (s : Set (Fin (r + 1) → K)), φ ⬝ᵥ w = 0`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact congrFun hφ ⟨x, hx⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]`. Use function extensionality and compare the values at `j`. Use `h0 (Pi.single j 1) (by rw [hspan]; exact Submodule.mem_top)` as an intermediate fact. Simplify using `using this`. Set `T : Submodule ℤ (s → K)` to `LinearMap.range (LinearMap.compLeft ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ) s)`.

Establish `hle : ((latticeDual F.lattice).restrictScalars ℤ).map ev ≤ T`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Establish `hv : ∀ v : s, (v : Fin (r + 1) → K) ∈ F.lattice`. Introduce `v`. Rewrite using `[← hs]`.

Conclude with `Submodule.subset_span v.2`. Use `⟨fun v ↦ (hφ v (hv v)).choose, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Conclude with `(hφ v (hv v)).choose_spec`. Establish `: IsNoetherian ℤ T` using `isNoetherian_of_isNoetherianRing_of_finite ℤ T`.

Conclude with `Submodule.fg_of_fg_map_injective ev hinj (isNoetherian_submodule.mp inferInstance _ hle)`.
-/
theorem latticeDual_int_fg {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ((latticeDual F.lattice).restrictScalars ℤ).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let ev : (Fin (r + 1) → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ v ↦ φ ⬝ᵥ (v : Fin (r + 1) → K)
      map_add' := by
        intro φ ψ
        funext v
        simp [add_dotProduct]
      map_smul' := by
        intro c φ
        funext v
        exact smul_dotProduct c φ (v : Fin (r + 1) → K) }
  have hspan : Submodule.span K (s : Set (Fin (r + 1) → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := 𝓞 K), hs, F.span_eq]
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    have h0 : ∀ w ∈ Submodule.span K (s : Set (Fin (r + 1) → K)), φ ⬝ᵥ w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact congrFun hφ ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
    funext j
    have := h0 (Pi.single j 1) (by rw [hspan]; exact Submodule.mem_top)
    simpa using this

  let T : Submodule ℤ (s → K) :=
    LinearMap.range (LinearMap.compLeft ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ) s)
  have hle : ((latticeDual F.lattice).restrictScalars ℤ).map ev ≤ T := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ v : s, (v : Fin (r + 1) → K) ∈ F.lattice := by
      intro v
      rw [← hs]
      exact Submodule.subset_span v.2
    refine ⟨fun v ↦ (hφ v (hv v)).choose, ?_⟩
    funext v
    exact (hφ v (hv v)).choose_spec
  have : IsNoetherian ℤ T := isNoetherian_of_isNoetherianRing_of_finite ℤ T
  exact Submodule.fg_of_fg_map_injective ev hinj (isNoetherian_submodule.mp inferInstance _ hle)

/- English proof (translation)
Take `⟨s, hs⟩` from `F.fg`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (s.image fun v ↦ v 0)`. Establish `hbne : algebraMap (𝓞 K) K b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Use `⟨Pi.single 0 (algebraMap (𝓞 K) K b), ?_, fun h ↦ hbne (by simpa using congrFun h 0)⟩` and prove the remaining obligations. Introduce `v hv`.

Rewrite `hv` using `[← hs]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha⟩` from `hb (x 0) (Finset.mem_image_of_mem _ hx)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[ha, Algebra.smul_def]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨c, hc⟩` from `hy`. Conclude with `⟨a + c, by rw [map_add, ha, hc, dotProduct_add]⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩`.
-/
theorem latticeDual_ne_bot {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ∃ ψ ∈ latticeDual F.lattice, ψ ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := F.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (s.image fun v ↦ v 0)
  have hbne : algebraMap (𝓞 K) K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Pi.single 0 (algebraMap (𝓞 K) K b), ?_, fun h ↦ hbne (by simpa using congrFun h 0)⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb (x 0) (Finset.mem_image_of_mem _ hx)
    refine ⟨a, ?_⟩
    rw [ha, Algebra.smul_def]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [map_add, ha, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩

/- English proof (translation)
Introduce `K _ _ r F`. Set `M : Submodule ℤ (Fin (r + 1) → K)` to `(latticeDual F.lattice).restrictScalars ℤ`. Establish `: Module.Finite ℤ M` using `Module.Finite.iff_fg.mpr (latticeDual_int_fg F)`. Establish `: Module.Free ℤ M` using `inferInstance`. Take `⟨ψ, hψ, hψ0⟩` from `latticeDual_ne_bot F`.

Establish `: Nontrivial M` using `⟨⟨⟨ψ, hψ⟩, 0, fun h ↦ hψ0 (congrArg Subtype.val h)⟩⟩`. Establish `hpos : 0 < Module.finrank ℤ M` using `Module.finrank_pos`. Take `⟨N, hN⟩ : ∃ N, Module.finrank ℤ M = N + 1` from `⟨Module.finrank ℤ M - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩`. Set `bas` to `Module.finBasisOfFinrankEq ℤ M hN`. Use `⟨N, fun i ↦ (bas i : Fin (r + 1) → K), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `bas.linearIndependent.map' M.subtype (Submodule.ker_subtype _)`. Establish `: Set.range (fun i ↦ (bas i : Fin (r + 1) → K)) = M.subtype '' Set.range bas`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, bas.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem DualBasisExists.proof : DualBasisExists.Statement := by
  intro K _ _ r F
  classical
  let M : Submodule ℤ (Fin (r + 1) → K) := (latticeDual F.lattice).restrictScalars ℤ
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr (latticeDual_int_fg F)
  have : Module.Free ℤ M := inferInstance
  obtain ⟨ψ, hψ, hψ0⟩ := latticeDual_ne_bot F
  have : Nontrivial M := ⟨⟨⟨ψ, hψ⟩, 0, fun h ↦ hψ0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank ℤ M := Module.finrank_pos
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℤ M = N + 1 :=
    ⟨Module.finrank ℤ M - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  let bas := Module.finBasisOfFinrankEq ℤ M hN
  refine ⟨N, fun i ↦ (bas i : Fin (r + 1) → K), ?_, ?_⟩
  · exact bas.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i ↦ (bas i : Fin (r + 1) → K)) = M.subtype '' Set.range bas := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, bas.span_eq, Submodule.map_top, Submodule.range_subtype]

end

end GroundTheory.Heights₂.Heights
