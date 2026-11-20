import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearSlotStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ht_combLine_integral_multiple : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  intro II hII Ψ _ N M t lam s q n W hn hW
  have hpos : 0 < degC W := GroundTheory.Heights₂.Heights.LowerBoundFree.degC_pos_of_isArithVar_one hW.1
  refine ⟨hpos, ?_⟩
  have hl : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hupd : ∀ B : HermLine M.ι, Function.update (![M.A] : Fin 1 → HermLine M.ι) 0 B = ![B] := by
    intro B
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  have hL : ∀ i, IsSmoothHerm ((![M.A] : Fin 1 → HermLine M.ι) i) := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact M.A_smooth
  have h := GlobalTheory.T.arith_intersection_multilinear II hII M.K M.ι W 1 ![M.A] 0 (Option (Ψ × Fin N)) (M.line t) n hW.1 hL hl
  simp only [hupd] at h
  have hd : (degC W : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h, RootModel.ht, mul_assoc, div_mul_cancel₀ _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hn j, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Top
