import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevelStatement

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : ‖u‖ ^ 2 ≤ (‖u + v‖ + ‖v‖) ^ 2` using `by gcongr`. Use polynomial arithmetic with `[sq_nonneg (2 * ‖u + v‖ - 13 * ‖v‖)]`.
-/
theorem splitCasRes_norm_sq_le_weighted {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u‖ ^ 2 ≤ 15 / 13 * ‖u + v‖ ^ 2 + 15 / 2 * ‖v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  have hsq : ‖u‖ ^ 2 ≤ (‖u + v‖ + ‖v‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * ‖u + v‖ - 13 * ‖v‖)]

/- English proof (translation)
Establish `hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2` using `by gcongr`. Conclude with `norm_add_le u v`. Use polynomial arithmetic with `[sq_nonneg (‖u‖ - ‖v‖)]`.
-/
theorem splitCasRes_norm_add_sq_le {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/- English proof (translation)
Establish `hb : 0 ≤ b`. Use `norm_nonneg (ζ + ((b / 16 : ℝ) : ℂ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : ζ + (t : ℂ) = (ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hshift : ‖((t - b / 16 : ℝ) : ℂ)‖ = |t - b / 16|`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[hsplit]`. Break down `ht with ⟨h1, h2⟩ | h3` into its components or cases.

Establish `hclose : |t - b / 16| ≤ 3 * b / 32`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `key` using `norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) ((t - b / 16 : ℝ) : ℂ)`. Rewrite `key` using `[add_sub_cancel_right, hζ, hshift]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfar : 33 * b / 32 ≤ |t - b / 16|`. Use `neg_le_abs (t - b / 16)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) (ζ + ((b / 16 : ℝ) : ℂ))`.

Rewrite `key` using `[add_sub_cancel_left, hζ, hshift]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem splitCasRes_circle_dist (b t : ℝ) (ζ : ℂ) (hζ : ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16)
    (ht : (-b / 8 - b / 32 ≤ -t ∧ -t ≤ b / 32) ∨ b - b / 32 ≤ -t) :
    15 * b / 32 ≤ ‖ζ + (t : ℂ)‖ := by
  have hb : 0 ≤ b := by
    have := norm_nonneg (ζ + ((b / 16 : ℝ) : ℂ))
    linarith
  have hsplit : ζ + (t : ℂ) = (ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ) := by
    push_cast
    ring
  have hshift : ‖((t - b / 16 : ℝ) : ℂ)‖ = |t - b / 16| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  rcases ht with ⟨h1, h2⟩ | h3
  ·
    have hclose : |t - b / 16| ≤ 3 * b / 32 := by
      rw [abs_le]
      constructor <;> linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) ((t - b / 16 : ℝ) : ℂ)
    rw [add_sub_cancel_right, hζ, hshift] at key
    linarith
  ·
    have hfar : 33 * b / 32 ≤ |t - b / 16| := by
      have := neg_le_abs (t - b / 16)
      linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) (ζ + ((b / 16 : ℝ) : ℂ))
    rw [add_sub_cancel_left, hζ, hshift] at key
    linarith

/- English proof (translation)
Introduce `M _ _ n ε E μ kk j bv x hmod hshape hj hlev`. Take `⟨hbv, hω, -⟩` from `shape_position n kk j ε μ bv hshape hj`. Establish `hun : IsUnitary ε E` using `hmod.2.1`. Establish `hoff : ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2` using `GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hmod hshape hj hlev`. Establish `hsplit : ∀ b, splitCas E x b = -(E b b (x b) + ∑ c ∈ univ.erase b, E b c (x c))`.

Introduce `b`. Simplify using `only [splitCas]`. Use `congr 1`. Conclude with `(Finset.add_sum_erase univ (fun c => E b c (x c)) (Finset.mem_univ b)).symm`. Establish `hdiag` using `fun c => wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hun (hlev c).2`.

Establish `hS : 0 ≤ ∑ c, ‖x c‖ ^ 2` using `Finset.sum_nonneg (fun _ _ => by positivity)`. Prove the components needed by the constructor for the conclusion. Introduce `ζ hζ`. Establish `hlow : ∀ b, (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 ≤ ‖ζ • x b + E b b (x b)‖ ^ 2`. Introduce `b`.

Use `(hdiag b).2.1 b ζ (15 * bv / 32) (by positivity) ?_` and prove the remaining obligations. Introduce `ω hωn`. Apply `splitCasRes_circle_dist bv (ω b) ζ hζ` to reduce the goal to its premises. Take `⟨h1, h2⟩` from `hω ω hωn b`. Distinguish the cases in `hb : b.val + 1 < kk`.

Conclude with `Or.inl (h1 hb)`. Conclude with `Or.inr (h2 (by omega)).1`. Establish `hper : ∀ b, 13 / 15 * (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 - 13 / 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ ‖ζ • x b - splitCas E x b‖ ^ 2`. Introduce `b`. Establish `hw` using `splitCasRes_norm_sq_le_weighted (ζ • x b + E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))`.

Establish `he : ζ • x b - splitCas E x b = (ζ • x b + E b b (x b)) + ∑ c ∈ univ.erase b, E b c (x c)`. Rewrite using `[hsplit]`. Normalize the expressions using the abelian group laws. Rewrite using `[he]`. Use polynomial arithmetic with `[hlow b]`.

Establish `hsum` using `Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)`. Rewrite `hsum` using `[Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`. Use polynomial arithmetic with `[hoff, hsum, mul_nonneg (sq_nonneg bv) hS]`. Establish `hD : ∀ b, ‖E b b (x b)‖ ^ 2 ≤ (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2`. Introduce `b`.

Use `(hdiag b).2.2 b (65 * bv / 32) ?_` and prove the remaining obligations. Introduce `ω hωn`. Take `⟨h1, h2⟩` from `hω ω hωn b`. Rewrite using `[abs_le]`. Distinguish the cases in `hb : b.val + 1 < kk`.

Take `⟨a1, a2⟩` from `h1 hb`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨a1, a2⟩` from `h2 (by omega)`. Apply the tactic sequence `constructor <;> linarith`. Establish `hper : ∀ b, ‖splitCas E x b‖ ^ 2 ≤ 2 * (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 + 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2`.

Introduce `b`. Rewrite using `[hsplit, norm_neg]`. Establish `ha` using `splitCasRes_norm_add_sq_le (E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))`. Use polynomial arithmetic with `[hD b]`. Establish `hsum` using `Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)`.

Rewrite `hsum` using `[Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`. Use polynomial arithmetic with `[hoff, hsum, mul_nonneg (sq_nonneg bv) hS]`.
-/
theorem splitCas_resolvent_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hshape hj hlev
  obtain ⟨hbv, hω, -⟩ := shape_position n kk j ε μ bv hshape hj
  have hun : IsUnitary ε E := hmod.2.1
  have hoff : ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 :=
    GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hmod hshape hj hlev
  have hsplit : ∀ b, splitCas E x b = -(E b b (x b) + ∑ c ∈ univ.erase b, E b c (x c)) := by
    intro b
    simp only [splitCas]
    congr 1
    exact (Finset.add_sum_erase univ (fun c => E b c (x c)) (Finset.mem_univ b)).symm
  have hdiag := fun c => wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hun (hlev c).2
  have hS : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  constructor
  · intro ζ hζ
    have hlow : ∀ b, (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 ≤ ‖ζ • x b + E b b (x b)‖ ^ 2 := by
      intro b
      refine (hdiag b).2.1 b ζ (15 * bv / 32) (by positivity) ?_
      intro ω hωn
      apply splitCasRes_circle_dist bv (ω b) ζ hζ
      obtain ⟨h1, h2⟩ := hω ω hωn b
      by_cases hb : b.val + 1 < kk
      · exact Or.inl (h1 hb)
      · exact Or.inr (h2 (by omega)).1
    have hper : ∀ b, 13 / 15 * (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2
        - 13 / 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ ‖ζ • x b - splitCas E x b‖ ^ 2 := by
      intro b
      have hw := splitCasRes_norm_sq_le_weighted (ζ • x b + E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      have he : ζ • x b - splitCas E x b
          = (ζ • x b + E b b (x b)) + ∑ c ∈ univ.erase b, E b c (x c) := by
        rw [hsplit]
        abel
      rw [he]
      nlinarith [hlow b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]
  · have hD : ∀ b, ‖E b b (x b)‖ ^ 2 ≤ (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 := by
      intro b
      refine (hdiag b).2.2 b (65 * bv / 32) ?_
      intro ω hωn
      obtain ⟨h1, h2⟩ := hω ω hωn b
      rw [abs_le]
      by_cases hb : b.val + 1 < kk
      · obtain ⟨a1, a2⟩ := h1 hb
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := h2 (by omega)
        constructor <;> linarith
    have hper : ∀ b, ‖splitCas E x b‖ ^ 2
        ≤ 2 * (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 + 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 := by
      intro b
      rw [hsplit, norm_neg]
      have ha := splitCasRes_norm_add_sq_le (E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      nlinarith [hD b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]

end GlobalTheory
