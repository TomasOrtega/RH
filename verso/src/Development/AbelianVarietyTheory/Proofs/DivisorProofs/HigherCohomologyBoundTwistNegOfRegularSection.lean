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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowthStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ X _ hX d L hL ih F _ hF B hB s hs hb i hi`. Use `haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX`. Establish `hcut : suppDim (cut F hB s) ≤ (d : ℕ)` using `suppDim_cut_le F hB s hF`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Establish `h1 : ∃ C : ℕ, ∀ m : ℕ, hdim k (twist (cut F hB s) (lbPow L m)) j ≤ C * ((d + 1) * (m + 1) ^ d)`.

Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Take `⟨C, hC⟩` from `GlobalTheory.T.global_sections_polynomial_growth k X hX d L hL (cut F hB s) hcut`. Conclude with `⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d)))⟩`. Take `⟨C, hC⟩` from `ih (cut F hB s) hcut j hj`. Conclude with `⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))))⟩`.

Take `⟨C₁, hC₁⟩` from `h1`. Take `⟨C₂, hC₂⟩` from `hb (j + 1) hi`. Use `⟨C₁ + C₂, fun m => ?_⟩` and prove the remaining obligations. Establish `hM : (lbPow L m).IsLB` using `isLB_lbPow hL m`. Establish `hB'` using `Twist.isLB_lbZPow hB (-1)`.

Take `⟨M', hM', e'⟩` from `cls_surj (cls _ hB' + cls _ hM)`. Take `⟨e⟩` from `nonempty_twist_twist_iso_of_cls_eq F hB' hM hM' e'`. Establish `key` using `(GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B (lbPow L m) M' hB hM hM' s hs (by`. Rewrite using `[e', cls_lbZPow hB]`. Use the proof step `simp)).2.1 j`.

Establish `e2 : hdim k (twist (twistZ F B (-1)) (lbPow L m)) (j + 1) = hdim k (twist F M') (j + 1)` using `hdim_congr k _ e`. Rewrite using `[e2, add_mul]`. Conclude with `key.trans (Nat.add_le_add (hC₁ m) (hC₂ m))`.
-/
theorem higherCohomology_bound_twist_neg_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL ih F _ hF B hB s hs hb i hi
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F hB s) ≤ (d : ℕ) := suppDim_cut_le F hB s hF
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 : ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (cut F hB s) (lbPow L m)) j ≤ C * ((d + 1) * (m + 1) ^ d) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨C, hC⟩ := GlobalTheory.T.global_sections_polynomial_growth k X hX d L hL (cut F hB s) hcut
      exact ⟨C, fun m => (hC m).trans
        (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d)))⟩
    · obtain ⟨C, hC⟩ := ih (cut F hB s) hcut j hj
      exact ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ d)
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))))⟩
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := hb (j + 1) hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  have hB' := Twist.isLB_lbZPow hB (-1)
  obtain ⟨M', hM', e'⟩ := cls_surj (cls _ hB' + cls _ hM)
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hB' hM hM' e'
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B (lbPow L m) M' hB hM hM' s hs (by
    rw [e', cls_lbZPow hB]; simp)).2.1 j
  have e2 : hdim k (twist (twistZ F B (-1)) (lbPow L m)) (j + 1) = hdim k (twist F M') (j + 1) :=
    hdim_congr k _ e
  rw [e2, add_mul]
  exact key.trans (Nat.add_le_add (hC₁ m) (hC₂ m))

end GlobalTheory
