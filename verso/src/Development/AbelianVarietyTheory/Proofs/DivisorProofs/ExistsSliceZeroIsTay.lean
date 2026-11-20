import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer.SliceZero

/- English proof (translation)
Distinguish the cases in `h : ∀ a, ∃ i, s a = Sum.inl i`. Use `choose f hf using h`. Rewrite using `[Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]`. Simplify using `using ht f`. Use `push_neg at h`.

Take `⟨a, ha⟩` from `h`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by`. Break down `hs : s a with i | b` into its components or cases. Conclude with `absurd hs (ha i)`. Conclude with `⟨b, rfl⟩`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)`.
-/
theorem prod_sumElim_zero {I : Type} {g : ℕ} {R : Type} [CommRing R] (N : ℕ) (t : I → R)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (s : Fin (N + 1) → I ⊕ Fin g) :
    ∏ a, (Sum.elim t (0 : Fin g → R)) (s a) = 0 := by
  by_cases h : ∀ a, ∃ i, s a = Sum.inl i
  · choose f hf using h
    rw [Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]
    simpa using ht f
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by
      rcases hs : s a with i | b
      · exact absurd hs (ha i)
      · exact ⟨b, rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)

end GlobalTheory.AnPer.SliceZero

open GlobalTheory.AnPer.SliceZero in

/- English proof (translation)
Introduce `I _ _ g R _ _ N t ht W W₀ hW`. Take `⟨ρ, hρ⟩` from `GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R)) (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd (fun p _ ↦ analyticAt_snd) hW`. Use `⟨ρ.toRingHom, fun h p hp ↦ ?_⟩` and prove the remaining obligations. Use `(hρ h p hp).trans ?_` and prove the remaining obligations. Establish `hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0)`.

Rewrite using `[add_zero]`. Conclude with `h.analytic _ (hW p hp)`. Establish `hs` using `taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh`. Simplify using `only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs`. Rewrite using `[hs]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.AnPer.exists_sliceZero_isTay : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  intro I _ _ g R _ _ N t ht W W₀ hW
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R))
    (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd
    (fun p _ ↦ analyticAt_snd) hW
  refine ⟨ρ.toRingHom, fun h p hp ↦ ?_⟩
  refine (hρ h p hp).trans ?_
  have hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0) := by
    rw [add_zero]; exact h.analytic _ (hW p hp)
  have hs := taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh
  simp only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs
  rw [hs]
  rfl
