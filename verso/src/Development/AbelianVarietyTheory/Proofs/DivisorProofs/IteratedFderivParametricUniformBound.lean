import Mathlib
open Set
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `E F _ _ _ _ S Φ A K hS hΦ hA hK hsub k`. Establish `hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Establish `hcont : ContinuousOn (iteratedFDeriv ℝ k Φ) S` using `(hΦ.continuousOn_iteratedFDerivWithin hk hS.uniqueDiffOn).congr (fun p hp => (iteratedFDerivWithin_of_isOpen k hS hp).symm)`. Take `⟨M, hM⟩` from `(hA.prod hK).exists_bound_of_continuousOn (hcont.mono hsub)`. Use `⟨M, fun ε hε x hx => ?_⟩` and prove the remaining obligations.

Establish `hp : (ε, x) ∈ S` using `hsub ⟨hε, hx⟩`. Use `set v : ℝ × E := (ε, 0) with hv`. Use `set g : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hg`. Use `set S' : Set (ℝ × E) := (fun p => p + v) ⁻¹' S with hS'`. Establish `hS'o : IsOpen S'` using `hS.preimage (continuous_id.add continuous_const)`.

Establish `hΦ' : ContDiffOn ℝ ∞ (fun p => Φ (p + v)) S'` using `hΦ.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)`. Establish `hgx : g x + v = (ε, x)` using `by simp [hg, hv]`. Establish `hxS : g x ∈ S'` using `by show g x + v ∈ S`. Rewrite using `[hgx]`. Conclude with `hp`.

Establish `hTo : IsOpen (g ⁻¹' S')` using `hS'o.preimage g.continuous`. Establish `hfun : (fun y => Φ (ε, y)) = (fun p => Φ (p + v)) ∘ g`. Use function extensionality and compare the values at `y`. Simplify using `[hg, hv]`. Establish `h1` using `g.iteratedFDerivWithin_comp_right hΦ' hS'o.uniqueDiffOn hTo.uniqueDiffOn hxS hk`.

Rewrite `h1` using `[iteratedFDerivWithin_of_isOpen k hTo (show x ∈ g ⁻¹' S' from hxS), iteratedFDerivWithin_of_isOpen k hS'o hxS, iteratedFDeriv_comp_add_right, hgx]`. Rewrite using `[hfun, h1]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Establish `hgn : ‖g‖ ≤ 1` using `ContinuousLinearMap.norm_inr_le_one ℝ ℝ E`. Establish `h2 : ∏ _i : Fin k, ‖g‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hgn)`.

Conclude with `(mul_le_of_le_one_right (norm_nonneg _) h2).trans (hM _ ⟨hε, hx⟩)`.
-/
theorem exists_bound_iteratedFDeriv_snd_of_isCompact_prod :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set (ℝ × E)} {Φ : ℝ × E → F} {A : Set ℝ} {K : Set E}, IsOpen S → ContDiffOn ℝ ∞ Φ S → IsCompact A → IsCompact K → A ×ˢ K ⊆ S → ∀ k : ℕ, ∃ M : ℝ, ∀ ε ∈ A, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (fun y => Φ (ε, y)) x‖ ≤ M := by
  intro E F _ _ _ _ S Φ A K hS hΦ hA hK hsub k
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcont : ContinuousOn (iteratedFDeriv ℝ k Φ) S :=
    (hΦ.continuousOn_iteratedFDerivWithin hk hS.uniqueDiffOn).congr
      (fun p hp => (iteratedFDerivWithin_of_isOpen k hS hp).symm)
  obtain ⟨M, hM⟩ := (hA.prod hK).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨M, fun ε hε x hx => ?_⟩
  have hp : (ε, x) ∈ S := hsub ⟨hε, hx⟩
  set v : ℝ × E := (ε, 0) with hv
  set g : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hg
  set S' : Set (ℝ × E) := (fun p => p + v) ⁻¹' S with hS'
  have hS'o : IsOpen S' := hS.preimage (continuous_id.add continuous_const)
  have hΦ' : ContDiffOn ℝ ∞ (fun p => Φ (p + v)) S' :=
    hΦ.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have hgx : g x + v = (ε, x) := by simp [hg, hv]
  have hxS : g x ∈ S' := by
    show g x + v ∈ S
    rw [hgx]; exact hp
  have hTo : IsOpen (g ⁻¹' S') := hS'o.preimage g.continuous
  have hfun : (fun y => Φ (ε, y)) = (fun p => Φ (p + v)) ∘ g := by
    funext y; simp [hg, hv]
  have h1 := g.iteratedFDerivWithin_comp_right hΦ' hS'o.uniqueDiffOn hTo.uniqueDiffOn hxS hk
  rw [iteratedFDerivWithin_of_isOpen k hTo (show x ∈ g ⁻¹' S' from hxS),
    iteratedFDerivWithin_of_isOpen k hS'o hxS, iteratedFDeriv_comp_add_right, hgx] at h1
  rw [hfun, h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hgn : ‖g‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ E
  have h2 : ∏ _i : Fin k, ‖g‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hgn)
  exact (mul_le_of_le_one_right (norm_nonneg _) h2).trans (hM _ ⟨hε, hx⟩)

end GlobalTheory
