import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory

open Filter Topology in
open scoped TensorProduct in

/- English proof (translation)
Introduce `LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall`. Take `⟨n, s, rfl⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp hT`. Use `set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ`. Establish `key : ∀ (a : ℕ) (c : Fin n → O), φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i`. Introduce `a c`.

Simplify using `only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul, algebraMap_smul]`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce `t ht`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).mp ht`.

Conclude with `⟨_, by rw [key 0 c, pow_zero, one_smul]⟩`. Establish `hq` using `IsModuleTopology.isOpenQuotientMap_of_surjective hsurj`. Use `⟨fun a => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Establish `hc : algebraMap O LL (lam ^ a) ≠ 0` using `by rw [map_pow]; exact pow_ne_zero _ hlam set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW`. Establish `hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL)`.

Use extensionality with `y`. Simplify using `[hW, map_mul]`. Establish `hWo : IsOpen W` using `hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen`. Establish `hPo : IsOpen (φ '' Set.univ.pi fun _ => W)` using `hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)`. Use `mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨y, hy, rfl⟩`. Use `choose c hc' using fun i => hy i (Set.mem_univ i)`. Establish `: y = fun i => algebraMap O LL (lam ^ a * c i)` using `funext fun i => (hc' i).symm`. Substitute `this` using the available equality. Conclude with `⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩`.

Establish `h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL)` using `hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)`. Rewrite `h0` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, t, ht, hsub⟩` from `h0`. Take `⟨a, ha⟩` from `hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)`. Use `⟨a, fun v hv => ?_⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).mp hv`. Rewrite using `[← key a c]`. Conclude with `hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i`.
-/
theorem _root_.GlobalTheory.lattice_multiples_nhds_basis :
    ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  intro LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ
  have key : ∀ (a : ℕ) (c : Fin n → O),
      φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i := by
    intro a c
    simp only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul,
      algebraMap_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ht
    exact ⟨_, by rw [key 0 c, pow_zero, one_smul]⟩
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  refine ⟨fun a => ?_, fun U hU => ?_⟩
  · have hc : algebraMap O LL (lam ^ a) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hlam
    set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW
    have hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL) := by
      ext y; simp [hW, map_mul]
    have hWo : IsOpen W := hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen
    have hPo : IsOpen (φ '' Set.univ.pi fun _ => W) :=
      hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)
    refine mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_
    rintro v ⟨y, hy, rfl⟩
    choose c hc' using fun i => hy i (Set.mem_univ i)
    have : y = fun i => algebraMap O LL (lam ^ a * c i) := funext fun i => (hc' i).symm
    subst this
    exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩
  · have h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL) :=
      hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hsub⟩ := h0
    obtain ⟨a, ha⟩ := hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hv
    rw [← key a c]
    exact hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i

end GlobalTheory
