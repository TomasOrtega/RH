import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hlpos : 0 < |t| / (2 * Real.sqrt ε)` using `div_pos (abs_pos.2 ht) (by have := Real.sqrt_pos.2 hε; positivity)`. Use `set l := |t| / (2 * Real.sqrt ε) with hl`. Establish `hk : ∀ u : E n, (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t u = (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)` using `fun u => kraw_eq ε hε t ht u`. Repeatedly rewrite using `[hk]`. Establish `h1 : ∫ β, ψ β * (((l ^ (n ^ 2) * gK (l • (w - β))) : ℝ) : ℂ) = ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)`.

Use `integral_sub_left_eq_self (μ := (volume : Measure (E n))) (fun u => ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)) w` as an intermediate fact. Simplify `this` using `only [sub_sub_cancel]`. Rewrite using `[h1]`. Establish `h2` using `Measure.integral_comp_smul (μ := (volume : Measure (E n))) (fun v : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ)) l`. Simplify using `only [inv_smul_smul₀ hlpos.ne'] at h2`.

Rewrite `h2` using `[finrank_E]`. Unfold `mM`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Simplify using `only`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((l ^ (n ^ 2) : ℝ) : ℂ) * (|(l ^ (n ^ 2))⁻¹| • ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)) := by rw [h2]`. Use `_ = ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ) := by`.

Rewrite using `[abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hlpos _).ne', Complex.ofReal_one, one_mul]`.
-/
theorem step_c (ψ : E n → ℂ) (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) (w : E n) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t (w - β)) =
      mM ψ (|t| / (2 * Real.sqrt ε)) w := by
  have hlpos : 0 < |t| / (2 * Real.sqrt ε) := div_pos (abs_pos.2 ht) (by have := Real.sqrt_pos.2 hε; positivity)
  set l := |t| / (2 * Real.sqrt ε) with hl
  have hk : ∀ u : E n, (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t u =
      (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := fun u => kraw_eq ε hε t ht u
  simp_rw [hk]
  have h1 : ∫ β, ψ β * (((l ^ (n ^ 2) * gK (l • (w - β))) : ℝ) : ℂ) =
      ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (E n)))
      (fun u => ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)) w
    simpa only [sub_sub_cancel] using this
  rw [h1]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure (E n))) (fun v : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ)) l
  simp only [inv_smul_smul₀ hlpos.ne'] at h2
  rw [finrank_E] at h2
  unfold mM
  calc ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)
      = ((l ^ (n ^ 2) : ℝ) : ℂ) * ∫ u, ψ (w - u) * (gK (l • u) : ℂ) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        push_cast
        ring
    _ = ((l ^ (n ^ 2) : ℝ) : ℂ) * (|(l ^ (n ^ 2))⁻¹| • ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)) := by rw [h2]
    _ = ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ) := by
        rw [abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (pow_pos hlpos _).ne', Complex.ofReal_one, one_mul]

end PositivityTheory.Rg.Sw.WR.D.Moll
