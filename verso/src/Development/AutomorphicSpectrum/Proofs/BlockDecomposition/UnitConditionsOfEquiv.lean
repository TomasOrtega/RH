import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitTransport

/- English proof (translation)
Introduce `G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h`. Unfold `GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢`. Take `⟨h1, h2, h3, h4⟩` from `h`. Use `⟨?_, (hK d).2 h2, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Rewrite using `[hf x, h1]`. Simplify using `only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]`. Unfold `GlobalTheory.BCT.cptPart`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `t ⟨ht, hc⟩`.

Rewrite using `[SetLike.mem_coe, hK t]`. Establish `hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d)`. Establish `htd : t * d = d * θ t` using `ht`. Use `show e t * e d = e d * θ' (e t)`. Rewrite using `[← hθ, ← map_mul e, ← map_mul e, htd]`.

Establish `hcl : closure (Subgroup.zpowers (e t) : Set G') = e '' closure (Subgroup.zpowers t : Set G)`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`. Use `⟨e.symm y, ?_, e.apply_symm_apply y⟩` and prove the remaining obligations. Use `map_mem_closure e.symm.continuous hy ?_` and prove the remaining obligations.

Introduce `z hz`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hz`. Conclude with `Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩`. Introduce and unpack `y ⟨x, hx, rfl⟩`. Use `map_mem_closure e.continuous hx ?_` and prove the remaining obligations.

Introduce `z hz`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hz`. Conclude with `Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩`. Establish `hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G'))`. Rewrite using `[hcl]`.

Conclude with `hc.image e.continuous`. Unfold `GlobalTheory.BCT.cptPart at h3`. Conclude with `h3 (Subgroup.subset_closure (And.intro hte hce))`. Introduce `y hy`. Establish `hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K'`.

Rewrite using `[← hθ, ← map_inv e, ← map_mul e, ← map_mul e]`. Conclude with `(hK _).1 hy`. Take `⟨t', ht', k', hk', hyt⟩` from `h4 (e y) hy'`. Use `⟨e.symm t', ?_, e.symm k', ?_, ?_⟩` and prove the remaining obligations. Use `show e.symm t' * d = d * θ (e.symm t')`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hθ, e.apply_symm_apply]`. Conclude with `ht'`. Rewrite using `[hK, e.apply_symm_apply]`. Conclude with `hk'`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `hyt`.
-/
theorem unitConds_of_homeo : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  unfold GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, (hK d).2 h2, ?_, ?_⟩
  · funext x
    rw [hf x, h1]
    simp only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]
  · unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    rw [SetLike.mem_coe, hK t]
    have hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d) := by
      have htd : t * d = d * θ t := ht
      show e t * e d = e d * θ' (e t)
      rw [← hθ, ← map_mul e, ← map_mul e, htd]
    have hcl : closure (Subgroup.zpowers (e t) : Set G') =
        e '' closure (Subgroup.zpowers t : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        refine map_mem_closure e.symm.continuous hy ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩
      · rintro y ⟨x, hx, rfl⟩
        refine map_mem_closure e.continuous hx ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩
    have hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
      rw [hcl]
      exact hc.image e.continuous
    unfold GlobalTheory.BCT.cptPart at h3
    exact h3 (Subgroup.subset_closure (And.intro hte hce))
  · intro y hy
    have hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K' := by
      rw [← hθ, ← map_inv e, ← map_mul e, ← map_mul e]
      exact (hK _).1 hy
    obtain ⟨t', ht', k', hk', hyt⟩ := h4 (e y) hy'
    refine ⟨e.symm t', ?_, e.symm k', ?_, ?_⟩
    · show e.symm t' * d = d * θ (e.symm t')
      apply e.injective
      rw [map_mul, map_mul, hθ, e.apply_symm_apply]
      exact ht'
    · rw [hK, e.apply_symm_apply]
      exact hk'
    · apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hyt

end GlobalTheory.CompanionTheory.UnitTransport
