import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

def lieSign (bot b : Bool) (m : ℕ) : ℚ := if bot = b then (-1) ^ m else -1

/- English proof (translation)
Unfold `lieSign`. Use `split_ifs`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℚ m with h | h <;> simp [h]`. Use `right`. Both sides reduce to the same expression.
-/
theorem lieSign_cases (bot b : Bool) (m : ℕ) : lieSign bot b m = 1 ∨ lieSign bot b m = -1 := by
  unfold lieSign
  split_ifs
  · rcases neg_one_pow_eq_or ℚ m with h | h <;> simp [h]
  · right; rfl

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.RestTerms.dimFl`. Establish `h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1)`. Break down `Nat.lt_or_ge (j + k) 2 with h | h` into its components or cases. Establish `: j + k - 1 = 0` using `by omega`. Simplify using `[this]`.

Rewrite using `[mul_comm (j + k)]`. Conclude with `Nat.mul_le_mul_left _ h`. Establish `h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2` using `(Nat.le_div_iff_mul_le (by norm_num)).2 h1`. Establish `h3 : (j + k) * (j + k - 1) / 2 ≤ f * ((j + k) * (j + k - 1) / 2)` using `Nat.le_mul_of_pos_left _ hf`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_dimFl (f j k : ℕ) (hf : 1 ≤ f) : j + k ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 := by
  unfold IndefiniteRowSideFullHecke.RestTerms.dimFl
  have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
    rcases Nat.lt_or_ge (j + k) 2 with h | h
    · have : j + k - 1 = 0 := by omega
      simp [this]
    · rw [mul_comm (j + k)]; exact Nat.mul_le_mul_left _ h
  have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
  have h3 : (j + k) * (j + k - 1) / 2 ≤ f * ((j + k) * (j + k - 1) / 2) :=
    Nat.le_mul_of_pos_left _ hf
  omega

/- English proof (translation)
Establish `hD` using `le_dimFl f j k hf`. Establish `hkill` using `hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega) (by convert hQ τ m (by omega) hmN using 1; omega)`. Establish `hsplit : IndefiniteRowSideFullHecke.RestTerms.psumAt f j k (m - 1) σ.1 = (∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ (m - 1)) + ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ (m - 1)`. Unfold `IndefiniteRowSideFullHecke.RestTerms.psumAt`. Conclude with `Fin.sum_univ_add _`.

Rewrite `hkill` using `[hsplit, add_mul, map_add]`. Take `⟨τ', b⟩` from `σ`. Break down `Nat.even_or_odd (m - 1) with he | ho` into its components or cases. Apply the tactic sequence `cases bot <;> cases b <;>`. Apply the tactic sequence `simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, he.neg_pow] <;> linarith`.

Apply the tactic sequence `cases bot <;> cases b <;>`. Apply the tactic sequence `simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, ho.neg_pow, Finset.sum_neg_distrib, neg_mul, map_neg] <;> linarith`.
-/
theorem lieClass_reduce (f j k : ℕ) (hf : 1 ≤ f) (bot : Bool)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : ∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 - m))
    (σ : Fin f × Bool) (τ : Fin f) (m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ j + k) :
    I (IndefiniteRowSideFullHecke.RestTerms.lieClass f j k (m - 1) σ * Q τ m) =
      (lieSign bot σ.2 (m - 1) : ℝ) *
        I (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) σ.1 * Q τ m) := by
  have hD := le_dimFl f j k hf
  have hkill := hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega)
    (by convert hQ τ m (by omega) hmN using 1; omega)
  have hsplit : IndefiniteRowSideFullHecke.RestTerms.psumAt f j k (m - 1) σ.1 =
      (∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ (m - 1)) +
        ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ (m - 1) := by
    unfold IndefiniteRowSideFullHecke.RestTerms.psumAt
    exact Fin.sum_univ_add _
  rw [hsplit, add_mul, map_add] at hkill
  obtain ⟨τ', b⟩ := σ
  rcases Nat.even_or_odd (m - 1) with he | ho
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, he.neg_pow] <;> linarith
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, ho.neg_pow,
        Finset.sum_neg_distrib, neg_mul, map_neg] <;> linarith

/- English proof (translation)
Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Establish `h` using `(isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)).pow m`. Rewrite `h` using `[one_mul]`. Conclude with `h`.
-/
theorem smallPowerSum_isHomogeneous (f r a : ℕ) (c : SmallBlock) (m : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c m τ).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h := (isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)).pow m
  rw [one_mul] at h
  exact h

/- English proof (translation)
Establish `h1` using `VandermondeOfHomogeneous.proof`. Establish `hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1` using `fun τ i => isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)`. Establish `hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1` using `fun τ i => isHomogeneous_X ℚ (zIndex f r a c τ i)`. Establish `hmu : (smallBlockMu f r a c).IsHomogeneous 1` using `IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i`. Establish `hfib : (fibreClass f r a c).IsHomogeneous (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2))` using `IsHomogeneous.prod _ _ _ fun τ _ => (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))`.

Establish `hF` using `(hmu.pow (f * (r * a))).mul hfib`. Establish `hdeg : 1 * (f * (r * a)) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) = topDegree f (r + a)`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree, choose_two_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hdeg]`.

Conclude with `hF`.
-/
theorem degPolynomial_isHomogeneous (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h1 := VandermondeOfHomogeneous.proof
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a))).mul hfib
  have hdeg : 1 * (f * (r * a)) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end RestBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
