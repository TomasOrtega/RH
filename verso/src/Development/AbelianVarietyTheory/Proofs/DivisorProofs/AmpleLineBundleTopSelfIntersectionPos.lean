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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.AmplePos

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Rewrite `ha` using `[not_lt]`. Take `⟨m, hm1, hm2⟩` from `(hf.and_eventually (eventually_ge_atTop (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists`. Establish `hmm₀ : m₀ ≤ m` using `le_trans (le_max_left _ _) hm2`. Establish `hm1' : 1 ≤ m` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2`.

Establish `hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2`. Establish `hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m`. Establish `h1` using `Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))`. Establish `h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m`. Conclude with `hmK'` after adjusting the coercions.

Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))`. Establish `h3` using `(abs_le.mp (hb m hmm₀)).2`. Establish `h4 : a * (m : ℤ) ^ d ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg ha (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1))`. Establish `h5` using `(Int.cast_le (R := ℝ)).mpr hint`. Move the coercions through the operations in `at h5`. Conclude with `h5`.

Establish `hF : (0 : ℝ) < d.factorial` using `by exact_mod_cast d.factorial_pos`. Establish `hmpos : (0 : ℝ) < m` using `by exact_mod_cast hm1'`. Break down `Nat.eq_zero_or_pos d with hd | hd` into its components or cases. Substitute `hd` using the available equality. Simplify using `only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero, pow_zero, mul_one] at hreal hm1`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨e, rfl⟩ : ∃ e, d = e + 1` from `⟨d - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel] at hreal hmK`. Establish `hm1r : (1 : ℝ) ≤ m` using `by exact_mod_cast hm1'`. Establish `h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) (by linarith) e`. Establish `hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c` using `mul_pos hF hc`. Rewrite `hmK` using `[div_lt_iff₀ hFc]`. Establish `h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤ (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ)` using `mul_le_mul_of_nonneg_left hm1 hF.le`.

Establish `hCpos : (0 : ℝ) ≤ C` using `by positivity`. Establish `h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤ (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e))`. Apply `mul_le_mul_of_nonneg_left _ hCpos` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left h5 (by positivity)`. Establish `hme : (0 : ℝ) < (m : ℝ) ^ e` using `by positivity`.

Establish `h8` using `mul_lt_mul_of_pos_right hmK hme`. Establish `h9 : (m : ℝ) ^ (e + 1) = m * m ^ e` using `by ring`. Rewrite `h6` using `[h9]`. Use polynomial arithmetic with `[h6, hreal, h7, h8]`.
-/
theorem pos_of_bound {h : ℕ → ℕ} {d C m₀ : ℕ} {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hf : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ h m)
    (hb : ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d| ≤
      C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) : 0 < a := by
  by_contra ha
  rw [not_lt] at ha
  obtain ⟨m, hm1, hm2⟩ := (hf.and_eventually (eventually_ge_atTop
    (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm2
  have hm1' : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  have hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m := by
    have h1 := Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))
    have h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hmK'
    push_cast at h2
    linarith
  have hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
    have h3 := (abs_le.mp (hb m hmm₀)).2
    have h4 : a * (m : ℤ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (by positivity)
    linarith
  have hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1)) := by
    have h5 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h5
    exact h5
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one] at hreal hm1
    linarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hreal hmK
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
    have h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) e
    have hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c := mul_pos hF hc
    rw [div_lt_iff₀ hFc] at hmK
    have h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤
        (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hF.le
    have hCpos : (0 : ℝ) ≤ C := by positivity
    have h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤
        (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hme : (0 : ℝ) < (m : ℝ) ^ e := by positivity
    have h8 := mul_lt_mul_of_pos_right hmK hme
    have h9 : (m : ℝ) ^ (e + 1) = m * m ^ e := by ring
    rw [h9] at h6
    nlinarith [h6, hreal, h7, h8]

/- English proof (translation)
Introduce `k _ _ X _ _ hp d hd A hA`. Take `⟨D, hD, c, hc, hf⟩` from `(IsAmpleLB.isBig k X hp A hA).growth`. Establish `hDd : D = d`. Rewrite `hd` using `[hD]`. Conclude with `hd` after adjusting the coercions.

Substitute `hDd` using the available equality. Establish `hsupp : suppDim (structureModule X) ≤ (D : ℕ)`. Unfold `GlobalTheory.QCoh.suppDim`. Rewrite using `[← hD]`. Conclude with `topologicalKrullDim_subspace_le _ _`.

Take `⟨C, m₀, hb⟩` from `GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA`. Rewrite using `[topSelf_def]`. Conclude with `pos_of_bound hc hf hb`.
-/
theorem topSelf_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) →
    ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  intro k _ _ X _ _ hp d hd A hA
  obtain ⟨D, hD, c, hc, hf⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDd : D = d := by
    rw [hD] at hd
    exact_mod_cast hd
  subst hDd
  have hsupp : suppDim (structureModule X) ≤ (D : ℕ) := by
    unfold GlobalTheory.QCoh.suppDim
    rw [← hD]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨C, m₀, hb⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA
  rw [topSelf_def]
  exact pos_of_bound hc hf hb

end GlobalTheory.AmplePos
