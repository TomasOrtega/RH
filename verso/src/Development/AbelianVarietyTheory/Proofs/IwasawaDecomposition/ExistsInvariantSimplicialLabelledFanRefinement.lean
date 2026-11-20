import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCellsStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `E _ _ _ H q ψ hD hψ hT`. Take `⟨lab, hlT, hlab⟩` from `GlobalTheory.T.exists_invariant_carrierDim_polyFan E H q ψ hD hψ hT`. Take `⟨N, hN⟩` from `GlobalTheory.T.polFanCarrierDimension_bounded E H q ψ lab hlab`. Establish `key : ∀ d : ℕ, ∃ φ : InvFun (𝓞 E), IsTwInv H φ ∧ IsBaryStage H.bar q ψ lab φ (N - d)`. Introduce `d`.

Proceed by induction on `d with`. Consider the case `zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩`. Consider the case `succ d ih`. Take `⟨φ, hφT, hφ⟩` from `ih`. Break down `Nat.eq_zero_or_pos (N - d) with h | h` into its components or cases.

Conclude with `⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩`. Establish `e : N - d = (N - (d + 1)) + 1` using `by omega`. Rewrite `hφ` using `[e]`. Conclude with `GlobalTheory.T.barycentricSubdivision_star_step_cells E H q ψ lab φ _ hD hψ hT hlT hlab hφT hφ`. Take `⟨φ, hφT, hφ⟩` from `key N`.

Rewrite `hφ` using `[Nat.sub_self]`. Conclude with `⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ H.bar q ψ lab φ hlab hφ, hφ.2.1⟩`.
-/
theorem exists_simpLab_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ lab : InvFun (𝓞 E), IsPolyFan H.bar q φ ∧ IsTwInv H φ ∧ IsTwInv H lab ∧ SimpLab H.bar q φ lab ∧ Subordinate H.bar q φ ψ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := GlobalTheory.T.exists_invariant_carrierDim_polyFan E H q ψ hD hψ hT
  obtain ⟨N, hN⟩ := GlobalTheory.T.polFanCarrierDimension_bounded E H q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun (𝓞 E), IsTwInv H φ ∧ IsBaryStage H.bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact GlobalTheory.T.barycentricSubdivision_star_step_cells E H q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ H.bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.PolFan
