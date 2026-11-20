import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hψ (by ext a; simp [h a])`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hy (AddChar.map_zero_eq_one ψ)`. Establish `hS' : {v : Fin n → k | Multiplicative.ofAdd v ∈ S} ∈ 𝓝 (0 : Fin n → k)` using `hS`. Take `⟨s, hs⟩` from `FourierPi.exists_box_subset hS'`. Use `⟨Units.mk0 y hy0 * s⁻¹, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hbox : x.toAdd ∈ FourierPi.box (Fin n) s`. Introduce `i _`. Use `show valuation k (x.toAdd i) ≤ valuation k (s : k)`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : valuation k (s : k) < valuation k (x.toAdd i)` using `not_le.mp hlt`.

Establish `hxi : x.toAdd i ≠ 0`. Introduce `h0`. Rewrite `hlt'` using `[h0, map_zero]`. Conclude with `not_lt_zero hlt'`. Establish `hmem : Multiplicative.ofAdd (Pi.single i (y / x.toAdd i) : Fin n → k) ∈ polyBall n (Units.mk0 y hy0 * s⁻¹)`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj show valuation k ((Pi.single j (y / x.toAdd j) : Fin n → k) j) ≤ valuation k ((Units.mk0 y hy0 * s⁻¹ : kˣ) : k)` using the available equality. Establish `hs0 : 0 < valuation k (s : k)` using `zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr s.ne_zero)`. Rewrite using `[Pi.single_eq_same, map_div₀, Units.val_mul, map_mul, Units.val_mk0, Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]`.

Conclude with `mul_le_mul_right ((inv_le_inv₀ (hs0.trans hlt') hs0).mpr hlt'.le) _`. Simplify using `[Pi.single_eq_of_ne hj, cball]`. Establish `h1` using `hx _ hmem`. Rewrite `h1` using `[toAdd_ofAdd, single_dotProduct, div_mul_cancel₀ _ hxi]`. Conclude with `hy h1`.

Conclude with `hs hbox`.
-/
theorem ann_subset_of_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ)
    {S : Set (Multiplicative (Fin n → k))} (hS : S ∈ 𝓝 (1 : Multiplicative (Fin n → k))) :
    ∃ t : kˣ, (ann ψ n t : Set (Multiplicative (Fin n → k))) ⊆ S := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext a; simp [h a])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (AddChar.map_zero_eq_one ψ)
  have hS' : {v : Fin n → k | Multiplicative.ofAdd v ∈ S} ∈ 𝓝 (0 : Fin n → k) := hS
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hS'
  refine ⟨Units.mk0 y hy0 * s⁻¹, fun x hx => ?_⟩
  have hbox : x.toAdd ∈ FourierPi.box (Fin n) s := by
    intro i _
    show valuation k (x.toAdd i) ≤ valuation k (s : k)
    by_contra hlt
    have hlt' : valuation k (s : k) < valuation k (x.toAdd i) := not_le.mp hlt
    have hxi : x.toAdd i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt'
      exact not_lt_zero hlt'
    have hmem : Multiplicative.ofAdd (Pi.single i (y / x.toAdd i) : Fin n → k) ∈ polyBall n
        (Units.mk0 y hy0 * s⁻¹) := by
      intro j
      by_cases hj : j = i
      · subst hj
        show valuation k ((Pi.single j (y / x.toAdd j) : Fin n → k) j) ≤
          valuation k ((Units.mk0 y hy0 * s⁻¹ : kˣ) : k)
        have hs0 : 0 < valuation k (s : k) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr s.ne_zero)
        rw [Pi.single_eq_same, map_div₀, Units.val_mul, map_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]
        exact mul_le_mul_right ((inv_le_inv₀ (hs0.trans hlt') hs0).mpr hlt'.le) _
      · simp [Pi.single_eq_of_ne hj, cball]
    have h1 := hx _ hmem
    rw [toAdd_ofAdd, single_dotProduct, div_mul_cancel₀ _ hxi] at h1
    exact hy h1
  exact hs hbox

end GlobalTheory.CompanionTheory.MirFourier

end
