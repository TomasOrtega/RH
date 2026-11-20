import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G W hW`. Take `⟨hWo, hWc, hWf⟩` from `hW`. Use `choose φ hφs hφd hφr using fun s => (hWo s).1.exists_contDiff_support_eq (n := ⊤)`. Establish `hnn : ∀ s x, 0 ≤ φ s x` using `fun s x => (hφr s ⟨x, rfl⟩).1`. Establish `hne : ∀ s x, φ s x ≠ 0 ↔ x ∈ W s` using `fun s x => by rw [← Function.mem_support, hφs]`.

Establish `hmulσ : ∀ (a b : Γ) (s : S), G.σ (a * b) s = G.σ a (G.σ b s)`. Introduce `a b s`. Rewrite using `[map_mul, Equiv.Perm.mul_apply]`. Establish `hmulρ : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x)`. Introduce `a b x`.

Rewrite using `[map_mul, ContinuousLinearMap.mul_apply]`. Set `Φ : S → V → ℝ` to `fun s p => ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)`. Establish `hinv : ∀ (δ : Γ) s p, Φ (G.σ δ⁻¹ s) (G.ρ δ⁻¹ p) = Φ s p`. Introduce `δ s p`. Use `show ∑ᶠ γ, φ (G.σ γ⁻¹ (G.σ δ⁻¹ s)) (G.ρ γ⁻¹ (G.ρ δ⁻¹ p)) = ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)`.

Rewrite using `[← finsum_comp_equiv (Equiv.mulLeft δ) (f := fun γ => φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))]`. Use `congr 1`. Use function extensionality and compare the values at `γ`. Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, hmulσ, hmulρ]`. Establish `hloc : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, ∃ F : Finset Γ, ∀ x ∈ N, ∀ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F`.

Introduce `s p hp`. Take `⟨N, hN, hNf⟩` from `hWf s p hp`. Conclude with `⟨N, hN, hNf.toFinset, fun x hx γ hγ => hNf.mem_toFinset.2 ⟨x, hx, (hne _ _).1 hγ⟩⟩`. Establish `hΦeq : ∀ s (F : Finset Γ) x, (∀ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F) → Φ s x = ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)` using `fun s F x h => finsum_eq_sum_of_support_subset _ (fun γ hγ => h γ hγ)`. Establish `hpos : ∀ s, ∀ p ∈ G.Y, 0 < Φ s p`.

Introduce `s p hp`. Take `⟨N, hN, F, hF⟩` from `hloc s p hp`. Rewrite using `[hΦeq s F p (hF p (mem_of_mem_nhds hN))]`. Take `⟨γ, hγ⟩` from `hWc s p hp`. Establish `h0 : φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) ≠ 0` using `(hne _ _).2 hγ`.

Conclude with `Finset.sum_pos' (fun i _ => hnn _ _) ⟨γ, hF p (mem_of_mem_nhds hN) γ h0, lt_of_le_of_ne (hnn _ _) (Ne.symm h0)⟩`. Establish `hsmooth : ∀ s, ∀ p ∈ G.Y, ContDiffAt ℝ ∞ (Φ s) p`. Introduce `s p hp`. Take `⟨N, hN, F, hF⟩` from `hloc s p hp`. Establish `hc : ContDiff ℝ ∞ (fun x => ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x))` using `ContDiff.sum (fun γ _ => (hφd _).comp (G.ρ γ⁻¹).contDiff)`.

Use `hc.contDiffAt.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hN] with x hx`. Conclude with `hΦeq s F x (hF x hx)`. Use `⟨fun s x => φ s x / Φ s x, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Conclude with `((hφd s).contDiffAt.div (hsmooth s p hp) (hpos s p hp).ne').contDiffWithinAt`. Take `⟨N, hN, hNf⟩` from `hWf s p hp`. Use `⟨N, hN, hNf.subset ?_⟩` and prove the remaining obligations. Introduce and unpack `γ ⟨x, hx, hne0⟩`. Conclude with `⟨x, hx, (hne _ _).1 (fun h => hne0 (by simp only [h, zero_div]))⟩`.

Establish `e : ∀ γ : Γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) * (Φ s p)⁻¹` using `fun γ => by rw [hinv, div_eq_mul_inv] show ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = 1`. Rewrite using `[finsum_congr e, ← finsum_mul]`. Conclude with `mul_inv_cancel₀ (hpos s p hp).ne'`.
-/
theorem cutoff : Cutoff := by
  intro Γ V S _ _ _ _ d G W hW
  obtain ⟨hWo, hWc, hWf⟩ := hW
  choose φ hφs hφd hφr using fun s => (hWo s).1.exists_contDiff_support_eq (n := ⊤)
  have hnn : ∀ s x, 0 ≤ φ s x := fun s x => (hφr s ⟨x, rfl⟩).1
  have hne : ∀ s x, φ s x ≠ 0 ↔ x ∈ W s := fun s x => by rw [← Function.mem_support, hφs]
  have hmulσ : ∀ (a b : Γ) (s : S), G.σ (a * b) s = G.σ a (G.σ b s) := by
    intro a b s
    rw [map_mul, Equiv.Perm.mul_apply]
  have hmulρ : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x) := by
    intro a b x
    rw [map_mul, ContinuousLinearMap.mul_apply]
  let Φ : S → V → ℝ := fun s p => ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)
  have hinv : ∀ (δ : Γ) s p, Φ (G.σ δ⁻¹ s) (G.ρ δ⁻¹ p) = Φ s p := by
    intro δ s p
    show ∑ᶠ γ, φ (G.σ γ⁻¹ (G.σ δ⁻¹ s)) (G.ρ γ⁻¹ (G.ρ δ⁻¹ p)) = ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ) (f := fun γ => φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))]
    congr 1
    funext γ
    simp only [Equiv.coe_mulLeft, mul_inv_rev, hmulσ, hmulρ]
  have hloc : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, ∃ F : Finset Γ, ∀ x ∈ N, ∀ γ,
      φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F := by
    intro s p hp
    obtain ⟨N, hN, hNf⟩ := hWf s p hp
    exact ⟨N, hN, hNf.toFinset, fun x hx γ hγ => hNf.mem_toFinset.2 ⟨x, hx, (hne _ _).1 hγ⟩⟩
  have hΦeq : ∀ s (F : Finset Γ) x, (∀ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F) →
      Φ s x = ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) :=
    fun s F x h => finsum_eq_sum_of_support_subset _ (fun γ hγ => h γ hγ)
  have hpos : ∀ s, ∀ p ∈ G.Y, 0 < Φ s p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    rw [hΦeq s F p (hF p (mem_of_mem_nhds hN))]
    obtain ⟨γ, hγ⟩ := hWc s p hp
    have h0 : φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) ≠ 0 := (hne _ _).2 hγ
    exact Finset.sum_pos' (fun i _ => hnn _ _)
      ⟨γ, hF p (mem_of_mem_nhds hN) γ h0, lt_of_le_of_ne (hnn _ _) (Ne.symm h0)⟩
  have hsmooth : ∀ s, ∀ p ∈ G.Y, ContDiffAt ℝ ∞ (Φ s) p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    have hc : ContDiff ℝ ∞ (fun x => ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) :=
      ContDiff.sum (fun γ _ => (hφd _).comp (G.ρ γ⁻¹).contDiff)
    refine hc.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    exact hΦeq s F x (hF x hx)
  refine ⟨fun s x => φ s x / Φ s x, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩
  · intro p hp
    exact ((hφd s).contDiffAt.div (hsmooth s p hp) (hpos s p hp).ne').contDiffWithinAt
  · obtain ⟨N, hN, hNf⟩ := hWf s p hp
    refine ⟨N, hN, hNf.subset ?_⟩
    rintro γ ⟨x, hx, hne0⟩
    exact ⟨x, hx, (hne _ _).1 (fun h => hne0 (by simp only [h, zero_div]))⟩
  · have e : ∀ γ : Γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) =
        φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) * (Φ s p)⁻¹ := fun γ => by rw [hinv, div_eq_mul_inv]
    show ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = 1
    rw [finsum_congr e, ← finsum_mul]
    exact mul_inv_cancel₀ (hpos s p hp).ne'

end UpperTheory.V.Lit.Dr
