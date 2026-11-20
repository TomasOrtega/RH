import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ _ n σ O _ φO W _ _ M j N hli hT`. Take `⟨hgen, hmem⟩` from `hT`. Establish `hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1)`. Introduce `x`. Use `conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective j`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx` using `[hj]`. Establish `h0` using `Fintype.linearIndependent_iff.1 hli _ hx`. Use function extensionality and compare the values at `i`.

Conclude with `σ.injective (by simpa using h0 i)`. Establish `hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v`. Introduce `v`. Distinguish the cases in `hv : v ∈ M.gen`. Take `⟨x, hx⟩` from `hgen v hv`.

Conclude with `⟨x, fun _ => hx⟩`. Conclude with `⟨0, fun h => absurd h hv⟩`. Use `choose pre hpre using hgen'`. Establish `hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W))`. Use extensionality with `x`.

Rewrite using `[hmem, Submodule.mem_span_image_finset_iff_exists_fun']`. Use `exists_congr fun a => ?_` and prove the remaining obligations. Establish `: ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]`. Rewrite using `[this]`. Conclude with `⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩`. Use `⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩` and prove the remaining obligations. Rewrite using `[hN]`.

Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance`. Set `B` to `Module.Basis.span hli`. Set `F0` to `B.constr ℂ (fun i => σ (f (Pi.single i 1)))`. Take `⟨F, hFF⟩` from `LinearMap.exists_extend F0`.

Establish `hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1))`. Introduce `i`. Establish `h1 : (B i : W) = j (Pi.single i 1)` using `by simp [B, Module.Basis.span_apply hli i]`. Rewrite using `[← h1]`. Establish `h2` using `LinearMap.congr_fun hFF (B i)`.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h2`. Rewrite using `[h2]`. Simplify using `[F0]`. Establish `hF : ∀ x, F (j x) = σ (f x)`. Introduce `x`.

Rewrite using `[hj, map_sum]`. Use `conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hFe]`.

Simplify using the standard rewrite rules. Establish `hF0 : F = 0`. Apply `LinearMap.ext_on M.span_top` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[← hpre v hv, hF]`.

Establish `: f (pre v) ∈ (⊥ : Submodule K K)`. Rewrite using `[← hf]`. Conclude with `Submodule.mem_map_of_mem (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))`. Rewrite using `[(Submodule.mem_bot K).1 this]`. Simplify using the standard rewrite rules.

Apply `hf0` to reduce the goal to its premises. Use `LinearMap.ext fun x => σ.injective ?_` and prove the remaining obligations. Rewrite using `[← hF, hF0]`. Simplify using the standard rewrite rules.
-/
theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x
    rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
