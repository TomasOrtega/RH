import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `f j k N e I c hcomp F Q₀ hQ₀ hQ₀h Q hQ m hm1 hmN τ G hG`. Establish `hNjk : N = j + k` using `by simpa using Fintype.card_congr e`. Substitute `hNjk` using the available equality. Establish `hf : 0 < f` using `Fin.pos τ`. Use `set E' : Fin f × (Fin j ⊕ Fin k) → Fin f × Fin (j + k) := fun p => (p.1, e.symm p.2) with hE'`.

Establish `hpr : ∀ x : RootPoly f j k, restRename f j k (j + k) e (rename E' x) = x`. Introduce `x`. Rewrite using `[restRename, rename_rename]`. Use `rename_id_apply x` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Simplify using `[hE']`. Establish `hrp : ∀ x : MvPolynomial (Fin f × Fin (j + k)) ℝ, rename E' (restRename f j k (j + k) e x) = x`. Introduce `x`. Rewrite using `[restRename, rename_rename]`. Use `rename_id_apply x` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `p`. Simplify using `[hE']`. Establish `hpsum : ∀ l σ, rename E' (rootPsum f j k l σ) = map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ)`. Introduce `l σ`. Rewrite using `[← h₃ f j k (j + k) e l σ]`.

Conclude with `hrp _`. Use `set R : ℕ → Fin f → MvPolynomial (Fin f × Fin (j + k)) ℝ := fun l σ => rename E' (Q σ l) - map (algebraMap ℚ ℝ) (Q₀ l σ) with hR`. Establish `hsyz : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f, map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * R l σ = 0`. Simplify using `only [hR, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`.

Establish `h1 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f, map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * rename E' (Q σ l) = rename E' (restTransport f j k (j + k) e F)`. Rewrite using `[hQ.2, map_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hpsum]`. Establish `h2 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f, map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * map (algebraMap ℚ ℝ) (Q₀ l σ) = map (algebraMap ℚ ℝ) F`. Rewrite using `[hQ₀]`. Simplify using `only [map_sum, map_mul]`. Rewrite using `[h1, h2]`.

Conclude with `hrp _`. Establish `hzero` using `h₁ f (j + k) R hsyz m hm1 hmN τ G hG`. Establish `hDle : j + k ≤ flagDim f j k + 1`. Establish `h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1)`. Break down `Nat.lt_or_ge (j + k) 2 with h | h` into its components or cases.

Apply the tactic sequence `interval_cases h : (j + k) <;> simp`. Rewrite using `[mul_comm]`. Conclude with `Nat.mul_le_mul_right _ h`. Establish `h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2` using `(Nat.le_div_iff_mul_le (by norm_num)).2 h1`. Establish `h3 : (j + k) * (j + k - 1) / 2 ≤ flagDim f j k`.

Unfold `flagDim`. Conclude with `Nat.le_mul_of_pos_left _ hf`. Use linear arithmetic over natural numbers and integers. Establish `hdeg : m - 1 + (flagDim f j k + 1 - m) = flagDim f j k` using `by omega`. Establish `hQh : (rename E' (Q τ m)).IsHomogeneous (flagDim f j k + 1 - m)` using `(hQ.1 τ m hm1 hmN).rename_isHomogeneous`.

Establish `hQ₀m` using `hQ₀h m τ hm1 hmN`. Establish `hsplit : restTransport f j k (j + k) e G * Q τ m = restRename f j k (j + k) e (map (algebraMap ℚ ℝ) G * R m τ) + restRename f j k (j + k) e (map (algebraMap ℚ ℝ) (G * Q₀ m τ))`. Rewrite using `[← map_add, hR]`. Simplify using `only`. Rewrite using `[map_mul (map (algebraMap ℚ ℝ)) G, ← mul_add, sub_add_cancel, map_mul, hpr]`.

Both sides reduce to the same expression. Rewrite using `[hsplit, map_add, hcomp _ ?_, hcomp _ ?_, hzero, (h₂ f (j + k)).1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hdeg]`. Conclude with `((hG.mul hQ₀m).map _)`.

Rewrite using `[← hdeg]`. Conclude with `(hG.map _).mul (hQh.sub (hQ₀m.map _))`.
-/
theorem RestCutTermEq.proof (h₁ : RestCutRealSyzygy.Statement) (h₂ : RestCutPsiFlag.Statement)
    (h₃ : RestCutTransportPsum.Statement) : RestCutTermEq.Statement := by
  intro f j k N e I c hcomp F Q₀ hQ₀ hQ₀h Q hQ m hm1 hmN τ G hG
  have hNjk : N = j + k := by simpa using Fintype.card_congr e
  subst hNjk
  have hf : 0 < f := Fin.pos τ
  set E' : Fin f × (Fin j ⊕ Fin k) → Fin f × Fin (j + k) := fun p => (p.1, e.symm p.2) with hE'
  have hpr : ∀ x : RootPoly f j k, restRename f j k (j + k) e (rename E' x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hrp : ∀ x : MvPolynomial (Fin f × Fin (j + k)) ℝ, rename E' (restRename f j k (j + k) e x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hpsum : ∀ l σ, rename E' (rootPsum f j k l σ) =
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) := by
    intro l σ
    rw [← h₃ f j k (j + k) e l σ]
    exact hrp _
  set R : ℕ → Fin f → MvPolynomial (Fin f × Fin (j + k)) ℝ :=
    fun l σ => rename E' (Q σ l) - map (algebraMap ℚ ℝ) (Q₀ l σ) with hR
  have hsyz : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * R l σ = 0 := by
    simp only [hR, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * rename E' (Q σ l) =
        rename E' (restTransport f j k (j + k) e F) := by
      rw [hQ.2, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, hpsum]
    have h2 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) *
          map (algebraMap ℚ ℝ) (Q₀ l σ) = map (algebraMap ℚ ℝ) F := by
      rw [hQ₀]
      simp only [map_sum, map_mul]
    rw [h1, h2]
    exact hrp _
  have hzero := h₁ f (j + k) R hsyz m hm1 hmN τ G hG
  have hDle : j + k ≤ flagDim f j k + 1 := by
    have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
      rcases Nat.lt_or_ge (j + k) 2 with h | h
      · interval_cases h : (j + k) <;> simp
      · rw [mul_comm]; exact Nat.mul_le_mul_right _ h
    have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    have h3 : (j + k) * (j + k - 1) / 2 ≤ flagDim f j k := by
      unfold flagDim; exact Nat.le_mul_of_pos_left _ hf
    omega
  have hdeg : m - 1 + (flagDim f j k + 1 - m) = flagDim f j k := by omega
  have hQh : (rename E' (Q τ m)).IsHomogeneous (flagDim f j k + 1 - m) :=
    (hQ.1 τ m hm1 hmN).rename_isHomogeneous
  have hQ₀m := hQ₀h m τ hm1 hmN
  have hsplit : restTransport f j k (j + k) e G * Q τ m =
      restRename f j k (j + k) e (map (algebraMap ℚ ℝ) G * R m τ) +
        restRename f j k (j + k) e (map (algebraMap ℚ ℝ) (G * Q₀ m τ)) := by
    rw [← map_add, hR]
    simp only
    rw [map_mul (map (algebraMap ℚ ℝ)) G, ← mul_add, sub_add_cancel, map_mul, hpr]
    rfl
  rw [hsplit, map_add, hcomp _ ?_, hcomp _ ?_, hzero, (h₂ f (j + k)).1]
  · ring
  · rw [← hdeg]; exact ((hG.mul hQ₀m).map _)
  · rw [← hdeg]
    exact (hG.map _).mul (hQh.sub (hQ₀m.map _))

end GroundTheory.Heights₂.Heights
