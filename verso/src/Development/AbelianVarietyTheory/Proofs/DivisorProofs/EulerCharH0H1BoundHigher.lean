import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

/- English proof (translation)
Introduce `k _ _ X _ hp n L hL F _ hF e he`. Use `choose C hC using fun i : ℕ => he (i + 2) (by omega)`. Use `⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩` and prove the remaining obligations. Establish `hM : (lbPow L m).IsLB` using `isLB_lbPow hL m`. Use `haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM`.

Establish `hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i)` using `fun i hi => subsingleton_coh_of_isProjOver hp _ (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))`. Rewrite using `[chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']`. Establish `h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a`. Introduce `a b c`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sum, Finset.sum_mul]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]`.

Conclude with `hC i m` after adjusting the coercions.
-/
theorem abs_chi_sub_hdim_zero_add_hdim_one_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  intro k _ _ X _ hp n L hL F _ hF e he
  choose C hC using fun i : ℕ => he (i + 2) (by omega)
  refine ⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM
  have hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i) := fun i hi =>
    subsingleton_coh_of_isProjOver hp _
      (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))
  rw [chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a := by
    intro a b c; ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  exact_mod_cast hC i m

end GlobalTheory.NefRR
