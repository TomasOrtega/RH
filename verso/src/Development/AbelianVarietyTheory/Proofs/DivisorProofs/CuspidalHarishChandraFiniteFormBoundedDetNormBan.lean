import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRapidDecayOneSimpleRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBoundsStatement

namespace GlobalTheory.HCF

open NumberField MeasureTheory GlobalTheory.CuspRep Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

/- English proof (translation)
Introduce `E _ _ _ a L hL W hW X hX N φ hφ hcusp`. Establish `hleft : ∀ ψ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g`. Introduce `ψ hψ γ g`. Proceed by induction on `hψ using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.1.left γ g`.

Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy`. Express the relevant statement in the definitionally equal form `x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g`. Rewrite using `[hx, hy]`. Consider the case `smul c x _ hx`.

Express the relevant statement in the definitionally equal form `c * x.1 (ratGL E a γ * g) = c * x.1 g`. Rewrite using `[hx]`. Take `⟨Ω, hΩc, hΩB, t, c₁, c₂, ht, hc₁, hred⟩` from `GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand E a`. Take `⟨C₀, N₀, hC₀, hpoly⟩` from `GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms E a L hL W X N φ hφ Ω hΩc`. Take `⟨β, hβ, hβc, hβs, hrep⟩` from `GlobalTheory.T.exists_test_function_reproducing_forms_gl E a L W hW X hX N`.

Take `⟨C', K, hC', hineq⟩` from `GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds a t c₁ c₂ ht hc₁`. Take `⟨Cm, hCm, hdec⟩` from `GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot E a L hL W X N β hβ hβc hβs hrep φ hφ hcusp Ω hΩc hΩB t C₀ N₀ ht hpoly (K * N₀)`. Use `⟨max (C₀ * C' ^ N₀ * height (1 : GL (Fin a) (Cinf E)) ^ N₀) (Cm * C' ^ N₀), fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, r, hr, hrat, hp1, hp2, k, hk, hg'⟩` from `hred g hg`. Rewrite using `[← hleft φ hφ γ g, hg']`.

Establish `hs0 : 0 ≤ ∑ i, (r i + (r i)⁻¹)` using `Finset.sum_nonneg fun i _ => by have := hr i; positivity`. Distinguish the cases in `hP : ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ 1 ≤ r i / r j`. Take `⟨i₀, j₀, hij₀, h1⟩` from `hP`. Take `⟨p, hpP, hpmax⟩` from `((Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1)).exists_max_image (fun p => r p.1 / r p.2) ⟨(i₀, j₀), by simp [hij₀]⟩`. Establish `hpP' : (p.2 : ℕ) = p.1 + 1` using `(Finset.mem_filter.1 hpP).2`.

Establish `hρ1 : 1 ≤ r p.1 / r p.2` using `le_trans h1 (hpmax (i₀, j₀) (by simp [hij₀]))`. Establish `hρ0 : 0 < r p.1 / r p.2` using `by linarith`. Establish `hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ (r p.1 / r p.2) * r j` using `fun i j hij => by`. Use `hpmax (i, j) (by simp [hij])` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (hr j)]`. Then use the resulting hypothesis.

Establish `hsle` using `hineq r hr hrat hp1 hp2 _ hρ1 hall`. Establish `hd` using `hdec b hb r hr hrat k hk p.1 p.2 hpP'`. Use `le_trans hd (le_trans ?_ (le_max_right _ _))` and prove the remaining obligations. Establish `e : r p.2 / r p.1 = (r p.1 / r p.2)⁻¹` using `by rw [inv_div]`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, inv_pow]`. Clear the denominators using the available nonvanishing facts. Use `push_neg at hP`. Establish `hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ 1 * r j` using `fun i j hij => by`.

Use `(hP i j hij).le` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (hr j)]`. Then use the resulting hypothesis. Establish `hsle` using `hineq r hr hrat hp1 hp2 1 le_rfl hall`. Rewrite `hsle` using `[one_pow, mul_one]`. Establish `hb'` using `hpoly b hb r hr k hk 1`.

Rewrite `hb'` using `[map_one, mul_one]`. Use `le_trans hb' (le_trans ?_ (le_max_left _ _))` and prove the remaining obligations. Establish `hh : 0 ≤ height (1 : GL (Fin a) (Cinf E))` using `le_trans zero_le_one (one_le_height _)`. Use `gcongr`.
-/
theorem bounded_on_band_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  intro E _ _ _ a L hL W hW X hX N φ hφ hcusp
  have hleft : ∀ ψ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g := by
    intro ψ hψ γ g
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy =>
      change x.1 (ratGL E a γ * g) + y.1 (ratGL E a γ * g) = x.1 g + y.1 g
      rw [hx, hy]
    | smul c x _ hx =>
      change c * x.1 (ratGL E a γ * g) = c * x.1 g
      rw [hx]
  obtain ⟨Ω, hΩc, hΩB, t, c₁, c₂, ht, hc₁, hred⟩ := GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand E a
  obtain ⟨C₀, N₀, hC₀, hpoly⟩ := GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms E a L hL W X N φ hφ Ω hΩc
  obtain ⟨β, hβ, hβc, hβs, hrep⟩ := GlobalTheory.T.exists_test_function_reproducing_forms_gl E a L W hW X hX N
  obtain ⟨C', K, hC', hineq⟩ := GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds a t c₁ c₂ ht hc₁
  obtain ⟨Cm, hCm, hdec⟩ := GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot E a L hL W X N β hβ hβc hβs hrep φ hφ hcusp Ω hΩc hΩB t C₀ N₀ ht hpoly (K * N₀)
  refine ⟨max (C₀ * C' ^ N₀ * height (1 : GL (Fin a) (Cinf E)) ^ N₀) (Cm * C' ^ N₀), fun g hg => ?_⟩
  obtain ⟨γ, b, hb, r, hr, hrat, hp1, hp2, k, hk, hg'⟩ := hred g hg
  rw [← hleft φ hφ γ g, hg']
  have hs0 : 0 ≤ ∑ i, (r i + (r i)⁻¹) := Finset.sum_nonneg fun i _ => by have := hr i; positivity
  by_cases hP : ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ 1 ≤ r i / r j
  · obtain ⟨i₀, j₀, hij₀, h1⟩ := hP
    obtain ⟨p, hpP, hpmax⟩ := ((Finset.univ : Finset (Fin a × Fin a)).filter
      (fun p => (p.2 : ℕ) = p.1 + 1)).exists_max_image (fun p => r p.1 / r p.2)
      ⟨(i₀, j₀), by simp [hij₀]⟩
    have hpP' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hpP).2
    have hρ1 : 1 ≤ r p.1 / r p.2 := le_trans h1 (hpmax (i₀, j₀) (by simp [hij₀]))
    have hρ0 : 0 < r p.1 / r p.2 := by linarith
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ (r p.1 / r p.2) * r j := fun i j hij => by
      have := hpmax (i, j) (by simp [hij])
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 _ hρ1 hall
    have hd := hdec b hb r hr hrat k hk p.1 p.2 hpP'
    refine le_trans hd (le_trans ?_ (le_max_right _ _))
    have e : r p.2 / r p.1 = (r p.1 / r p.2)⁻¹ := by rw [inv_div]
    rw [e]
    calc Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (∑ i, (r i + (r i)⁻¹)) ^ N₀
        ≤ Cm * (r p.1 / r p.2)⁻¹ ^ (K * N₀) * (C' * (r p.1 / r p.2) ^ K) ^ N₀ := by
          gcongr
      _ = Cm * C' ^ N₀ := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp
  · push_neg at hP
    have hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ 1 * r j := fun i j hij => by
      have := (hP i j hij).le
      rwa [div_le_iff₀ (hr j)] at this
    have hsle := hineq r hr hrat hp1 hp2 1 le_rfl hall
    rw [one_pow, mul_one] at hsle
    have hb' := hpoly b hb r hr k hk 1
    rw [map_one, mul_one] at hb'
    refine le_trans hb' (le_trans ?_ (le_max_left _ _))
    have hh : 0 ≤ height (1 : GL (Fin a) (Cinf E)) := le_trans zero_le_one (one_le_height _)
    gcongr

end GlobalTheory.HCF
