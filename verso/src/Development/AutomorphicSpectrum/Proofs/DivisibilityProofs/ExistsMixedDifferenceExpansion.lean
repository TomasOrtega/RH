import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `s hs`. Establish `hs0 : s = 0` using `(Finsupp.degree_eq_zero_iff s).mp hs`. Substitute `hs0` using the available equality.

Use `⟨fun _ => 0, ?_, fun i => ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩⟩` and prove the remaining obligations. Simplify using `[mixDiff]`. Consider the case `succ d ih`. Introduce `s hs`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, s i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : s = 0` using `Finsupp.ext h`. Simplify using `[h0] at hs`. Establish `hle : Finsupp.single i 1 ≤ s`.

Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Take `⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single i 1` from `⟨s - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩`. Establish `hdeg : s'.degree = d`. Establish `e : (s' + Finsupp.single i 1).degree = s'.degree + 1`.

Rewrite using `[Finsupp.degree_eq_weight_one, map_add]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_single_index]`. Use linear arithmetic over natural numbers and integers. Take `⟨G', hG', hG'h⟩` from `ih s' hdeg`. Use `⟨fun j => (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0) + X (Sum.inr i) * G' j, ?_, fun j => ⟨?_, fun h => absurd h (Nat.succ_ne_zero d)⟩⟩` and prove the remaining obligations.

Establish `key : mixDiff (monomial (s' + Finsupp.single i 1) (1 : ℝ)) = (X (Sum.inl i) - X (Sum.inr i)) * rename Sum.inl (monomial s' (1 : ℝ)) + X (Sum.inr i) * mixDiff (monomial s' (1 : ℝ))`. Simplify using `only [mixDiff]`. Rewrite using `[monomial_add_single, pow_one, map_mul, map_mul, rename_X, rename_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hG', Finset.mul_sum]`.

Simplify using `only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `h2 : (X (Sum.inr i) * G' j : MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d`. Break down `Nat.eq_zero_or_pos d with h0 | hpos` into its components or cases.

Rewrite using `[(hG'h j).2 h0, mul_zero]`. Conclude with `isHomogeneous_zero _ _ _`. Establish `h3` using `(isHomogeneous_X ℝ (Sum.inr i : σ ⊕ σ)).mul (hG'h j).1`. Rewrite `h3` using `[show 1 + (d - 1) = d by omega]`. Then use the resulting hypothesis. Establish `h1 : (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0 : MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d` using `by split_ifs`.

Conclude with `(isHomogeneous_monomial _ hdeg).rename_isHomogeneous`. Conclude with `isHomogeneous_zero _ _ _`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `h1.add h2`.
-/
theorem exists_monomial_mixExpansion {σ : Type} [Fintype σ] (d : ℕ) :
    ∀ s : σ →₀ ℕ, s.degree = d → ∃ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ,
      mixDiff (monomial s (1 : ℝ)) = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i ∧
      ∀ i, (Gs i).IsHomogeneous (d - 1) ∧ (d = 0 → Gs i = 0) := by
  classical
  induction d with
  | zero =>
    intro s hs
    have hs0 : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst hs0
    refine ⟨fun _ => 0, ?_, fun i => ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩⟩
    simp [mixDiff]
  | succ d ih =>
    intro s hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra h
      push_neg at h
      have h0 : s = 0 := Finsupp.ext h
      simp [h0] at hs
    have hle : Finsupp.single i 1 ≤ s := by
      rw [Finsupp.single_le_iff]
      omega
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single i 1 :=
      ⟨s - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩
    have hdeg : s'.degree = d := by
      have e : (s' + Finsupp.single i 1).degree = s'.degree + 1 := by
        rw [Finsupp.degree_eq_weight_one, map_add]
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      omega
    obtain ⟨G', hG', hG'h⟩ := ih s' hdeg
    refine ⟨fun j => (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0) + X (Sum.inr i) * G' j,
      ?_, fun j => ⟨?_, fun h => absurd h (Nat.succ_ne_zero d)⟩⟩
    · have key : mixDiff (monomial (s' + Finsupp.single i 1) (1 : ℝ)) =
          (X (Sum.inl i) - X (Sum.inr i)) * rename Sum.inl (monomial s' (1 : ℝ)) +
            X (Sum.inr i) * mixDiff (monomial s' (1 : ℝ)) := by
        simp only [mixDiff]
        rw [monomial_add_single, pow_one, map_mul, map_mul, rename_X, rename_X]
        ring
      rw [key, hG', Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    · have h2 : (X (Sum.inr i) * G' j : MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · rw [(hG'h j).2 h0, mul_zero]
          exact isHomogeneous_zero _ _ _
        · have h3 := (isHomogeneous_X ℝ (Sum.inr i : σ ⊕ σ)).mul (hG'h j).1
          rwa [show 1 + (d - 1) = d by omega] at h3
      have h1 : (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0 :
          MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        split_ifs
        · exact (isHomogeneous_monomial _ hdeg).rename_isHomogeneous
        · exact isHomogeneous_zero _ _ _
      rw [Nat.add_sub_cancel]
      exact h1.add h2

/- English proof (translation)
Establish `H` using `fun s : σ →₀ ℕ => fun h : s.degree = n => exists_monomial_mixExpansion n s h`. Use `choose! G hGeq hGhom using H`. Establish `hdeg : ∀ s ∈ F.support, s.degree = n` using `fun s hs => by`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hF (mem_support_iff.mp hs)`.

Establish `hlin : mixDiff F = ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ))` using `by conv_lhs => rw [F.as_sum]`. Simplify using `only [mixDiff, map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[show monomial s (F.coeff s) = C (F.coeff s) * monomial s (1 : ℝ) by rw [C_mul_monomial, mul_one], map_mul, map_mul, rename_C, rename_C]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun i => ∑ s ∈ F.support, C (F.coeff s) * G s i, ?_⟩` and prove the remaining obligations. Unfold `IsMixExpansion`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hlin]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring`. Conclude with `IsHomogeneous.sum _ _ _ fun s hs => ((hGhom s (hdeg s hs) i).1).C_mul _`.
-/
theorem exists_mixExpansion_mixDiff (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ)
    (hF : F.IsHomogeneous n) : ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  classical
  have H := fun s : σ →₀ ℕ => fun h : s.degree = n => exists_monomial_mixExpansion n s h
  choose! G hGeq hGhom using H
  have hdeg : ∀ s ∈ F.support, s.degree = n := fun s hs => by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hs)
  have hlin : mixDiff F = ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ)) := by
    conv_lhs => rw [F.as_sum]
    simp only [mixDiff, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show monomial s (F.coeff s) = C (F.coeff s) * monomial s (1 : ℝ) by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, rename_C, rename_C]
    ring
  refine ⟨fun i => ∑ s ∈ F.support, C (F.coeff s) * G s i, ?_⟩
  unfold IsMixExpansion
  refine ⟨?_, fun i => ?_⟩
  · rw [hlin]
    calc ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ))
        = ∑ s ∈ F.support, C (F.coeff s) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * G s i :=
          Finset.sum_congr rfl fun s hs => by rw [hGeq s (hdeg s hs)]
      _ = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * ∑ s ∈ F.support, C (F.coeff s) * G s i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  · exact IsHomogeneous.sum _ _ _ fun s hs => ((hGhom s (hdeg s hs) i).1).C_mul _
end

end GlobalTheory.CompanionTheory.Ar.Num
