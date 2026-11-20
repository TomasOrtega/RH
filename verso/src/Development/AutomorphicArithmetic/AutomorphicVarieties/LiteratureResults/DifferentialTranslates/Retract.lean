import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BasicDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltAddRadial
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullEquiv

open UpperTheory.V.Lit.Dr
open scoped ContDiff

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hY l hl q η hη hd`. Take `⟨hgauge, hinv⟩` from `hl`. Establish `hmem : ∀ s, ContDiffOn ℝ ∞ ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧ ∀ p ∉ G.Y, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0` using `η.2`. Establish `hmem' : ∀ s, ContDiffOn ℝ ∞ (((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧ ∀ p ∉ G.Y, ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p = 0` using `((G.dOm q) η).2`. Set `w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)` to `fun s => G.Y.indicator (pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))`.

Establish `hwmem : w ∈ G.Om q` using `by show ∀ s, ContDiffOn ℝ ∞ (w s) G.Y ∧ ∀ p ∉ G.Y, w s p = 0`. Introduce `s`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).1.congr ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [w, Set.indicator_of_mem hp]`. Introduce `p hp`. Simplify using `only [w, Set.indicator_of_notMem hp]`. Use `⟨⟨w, hwmem⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Use `show (G.tr q γ) (w ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p)) = w s p`. Distinguish the cases in `hp : p ∈ G.Y`. Establish `hp' : (G.ρ γ⁻¹) p ∈ G.Y` using `G.maps _ _ hp`.

Simplify using `only [w, Set.indicator_of_mem hp, Set.indicator_of_mem hp']`. Conclude with `pullEquiv Γ V S d G hY l ⟨hgauge, hinv⟩ q η hη γ s p hp`. Establish `hback : (G.ρ γ) ((G.ρ γ⁻¹) p) = p`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.

Establish `hp' : (G.ρ γ⁻¹) p ∉ G.Y`. Introduce `h`. Conclude with `hp (hback ▸ G.maps γ _ h)`. Simplify using `only [w, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp', map_zero]`. Introduce `s p hp v i hv show w s p v = 0`.

Simplify using `only [w, Set.indicator_of_mem hp]`. Conclude with `(pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _).1 p hp v i hv`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Use `show G.Y.indicator (extDeriv (w s)) p = ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p`.

Use `set u := ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s with hu_def`. Establish `hu : u = G.Y.indicator (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))` using `rfl`. Distinguish the cases in `hp : p ∈ G.Y`. Rewrite using `[Set.indicator_of_mem hp]`. Establish `hev : w s =ᶠ[nhds p] pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)` using `by filter_upwards [G.isOpen.mem_nhds hp] with x hx`.

Simplify using `only [w, Set.indicator_of_mem hx]`. Rewrite using `[hev.extDeriv_eq, (pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).2 p hp]`. Establish `hq : l s p • p ∈ G.Y` using `hY _ ((hgauge s).2.1 p hp) p hp`. Establish `hpu : pull (l s) (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p = pull (l s) u p`. Simplify using `only [pull, hu, Set.indicator_of_mem hq]`.

Establish `hsm : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞)`. Simplify using `only [minSmoothness_of_isRCLikeNormedField]`. Conclude with `WithTop.coe_le_coe.2 le_top`. Establish `hclosed : ∀ x ∈ G.Y, extDeriv u x = 0`. Introduce `x hx`.

Establish `hev2 : u =ᶠ[nhds x] extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)` using `by filter_upwards [G.isOpen.mem_nhds hx] with y hy`. Rewrite using `[hu, Set.indicator_of_mem hy]`. Rewrite using `[hev2.extDeriv_eq]`. Conclude with `extDeriv_extDeriv_apply ((hmem s).1.contDiffAt (G.isOpen.mem_nhds hx)) hsm`. Establish `hhom` using `homog V (Fin d → ℂ) G.Y G.isOpen hY (q + 1) u (hmem' s).1 (hd s) hclosed`.

Rewrite using `[hpu, (pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) (q + 1) u).2 (hd s) hhom p hp]`. Rewrite using `[Set.indicator_of_notMem hp]`. Conclude with `((hmem' s).2 p hp).symm`.
-/
theorem UpperTheory.V.Lit.Dr.retract :
    Retract := by
  intro Γ V S _ _ _ _ d G hY l hl q η hη hd
  classical
  obtain ⟨hgauge, hinv⟩ := hl
  have hmem : ∀ s, ContDiffOn ℝ ∞ ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := η.2
  have hmem' : ∀ s, ContDiffOn ℝ ∞ (((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    ((G.dOm q) η).2
  let w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s => G.Y.indicator (pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))
  have hwmem : w ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (w s) G.Y ∧ ∀ p ∉ G.Y, w s p = 0
    intro s
    refine ⟨?_, ?_⟩
    · refine (pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).1.congr ?_
      intro p hp
      simp only [w, Set.indicator_of_mem hp]
    · intro p hp
      simp only [w, Set.indicator_of_notMem hp]
  refine ⟨⟨w, hwmem⟩, ?_, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show (G.tr q γ) (w ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p)) = w s p
    by_cases hp : p ∈ G.Y
    · have hp' : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ _ hp
      simp only [w, Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      exact pullEquiv Γ V S d G hY l ⟨hgauge, hinv⟩ q η hη γ s p hp
    · have hback : (G.ρ γ) ((G.ρ γ⁻¹) p) = p := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have hp' : (G.ρ γ⁻¹) p ∉ G.Y := by
        intro h
        exact hp (hback ▸ G.maps γ _ h)
      simp only [w, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp', map_zero]
  · intro s p hp v i hv
    show w s p v = 0
    simp only [w, Set.indicator_of_mem hp]
    exact (pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _).1 p hp v i hv
  · apply Subtype.ext
    funext s p
    show G.Y.indicator (extDeriv (w s)) p =
      ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    set u := ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s with hu_def
    have hu : u = G.Y.indicator (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) := rfl
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp]
      have hev : w s =ᶠ[nhds p] pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) := by
        filter_upwards [G.isOpen.mem_nhds hp] with x hx
        simp only [w, Set.indicator_of_mem hx]
      rw [hev.extDeriv_eq, (pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).2 p hp]
      have hq : l s p • p ∈ G.Y := hY _ ((hgauge s).2.1 p hp) p hp
      have hpu : pull (l s) (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p =
          pull (l s) u p := by
        simp only [pull, hu, Set.indicator_of_mem hq]
      have hsm : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 le_top
      have hclosed : ∀ x ∈ G.Y, extDeriv u x = 0 := by
        intro x hx
        have hev2 : u =ᶠ[nhds x] extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) := by
          filter_upwards [G.isOpen.mem_nhds hx] with y hy
          rw [hu, Set.indicator_of_mem hy]
        rw [hev2.extDeriv_eq]
        exact extDeriv_extDeriv_apply ((hmem s).1.contDiffAt (G.isOpen.mem_nhds hx)) hsm
      have hhom := homog V (Fin d → ℂ) G.Y G.isOpen hY (q + 1) u (hmem' s).1 (hd s) hclosed
      rw [hpu, (pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) (q + 1) u).2 (hd s) hhom p hp]
    · rw [Set.indicator_of_notMem hp]
      exact ((hmem' s).2 p hp).symm
