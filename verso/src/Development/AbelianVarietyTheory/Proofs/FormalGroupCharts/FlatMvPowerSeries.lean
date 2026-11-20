import Mathlib

open MvPowerSeries IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.PowerSeriesFlat

/- English proof (translation)
Apply `Module.Flat.of_forall_isTrivialRelation` to reduce the goal to its premises. Introduce `l f x h`. Set `φ : (Fin l → T) →ₗ[T] T` to `Fintype.linearCombination T f`. Establish `hφ : ∀ v : Fin l → T, φ v = ∑ i, f i * v i`. Introduce `v`.

Simplify using `[φ, Fintype.linearCombination_apply, mul_comm]`. Establish `hfg : (LinearMap.ker φ).FG` using `IsNoetherian.noetherian _`. Take `⟨k, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Establish `hx : ∀ t : ι, ∃ c : Fin k → T, ∑ j, c j • s j = fun i => x i t`. Introduce `t`.

Establish `hm : (fun i => x i t) ∈ LinearMap.ker φ`. Rewrite using `[LinearMap.mem_ker, hφ]`. Use `congrFun h t` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Rewrite `hm` using `[← hs]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun T).1 hm`. Use `choose c hc using hx`. Use `⟨k, fun i j => s j i, fun j t => c t j, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use function extensionality and compare the values at `t`.

Use `congrFun (hc t) i` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Introduce `j`.

Establish `hm : s j ∈ LinearMap.ker φ`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Rewrite `hm` using `[LinearMap.mem_ker, hφ]`. Then use the resulting hypothesis.
-/
theorem flat_pi (T : Type*) [CommRing T] [IsNoetherianRing T] (ι : Type*) :
    Module.Flat T (ι → T) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x h
  let φ : (Fin l → T) →ₗ[T] T := Fintype.linearCombination T f
  have hφ : ∀ v : Fin l → T, φ v = ∑ i, f i * v i := by
    intro v
    simp [φ, Fintype.linearCombination_apply, mul_comm]
  have hfg : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hx : ∀ t : ι, ∃ c : Fin k → T, ∑ j, c j • s j = fun i => x i t := by
    intro t
    have hm : (fun i => x i t) ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφ]
      have := congrFun h t
      simpa [Finset.sum_apply] using this
    rw [← hs] at hm
    exact (Submodule.mem_span_range_iff_exists_fun T).1 hm
  choose c hc using hx
  refine ⟨k, fun i j => s j i, fun j t => c t j, ?_, ?_⟩
  · intro i
    funext t
    have := congrFun (hc t) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j
    have hm : s j ∈ LinearMap.ker φ := by
      rw [← hs]
      exact Submodule.subset_span ⟨j, rfl⟩
    rwa [LinearMap.mem_ker, hφ] at hm

/- English proof (translation)
Introduce `T _ _ σ` and use `flat_pi T (σ →₀ ℕ)`.
-/
theorem flat_mvPowerSeries :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  fun T _ _ σ => flat_pi T (σ →₀ ℕ)

end GlobalTheory.PowerSeriesFlat
