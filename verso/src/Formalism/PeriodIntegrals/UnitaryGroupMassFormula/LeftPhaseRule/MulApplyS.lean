import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

def SP (k r : ℕ) (l : Fin r) (p q : Fin (2 * r + k + 1)) : Prop :=
  (p.val = l.val ∧ l.val < q.val ∧ q.val ≤ 2 * r + k - l.val) ∨
  (q.val = 2 * r + k - l.val ∧ l.val < p.val ∧ p.val < 2 * r + k - l.val)

def InS (k r : ℕ) (l : Fin r) (M : Mx k r) : Prop := ∀ p q, ¬ SP k r l p q → M p q = 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma eI_val (a : Fin r) : (eI k r a).val = a.val := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

/- English proof (translation)
Introduce `p q h` and use `by rw [Matrix.add_apply, hM p q h, hN p q h, add_zero]`.
-/
lemma inS_add {l : Fin r} {M N : Mx k r} (hM : InS k r l M) (hN : InS k r l N) :
    InS k r l (M + N) := fun p q h => by
  rw [Matrix.add_apply, hM p q h, hN p q h, add_zero]

/- English proof (translation)
Introduce `p q h` and use `by rw [Matrix.sub_apply, hM p q h, hN p q h, sub_zero]`.
-/
lemma inS_sub {l : Fin r} {M N : Mx k r} (hM : InS k r l M) (hN : InS k r l N) :
    InS k r l (M - N) := fun p q h => by
  rw [Matrix.sub_apply, hM p q h, hN p q h, sub_zero]

/- English proof (translation)
Introduce `p q h` and use `by rw [Matrix.smul_apply, hM p q h, smul_zero]`.
-/
lemma inS_smul {l : Fin r} {M : Mx k r} (s : ℂ) (hM : InS k r l M) : InS k r l (s • M) := fun p q h => by
  rw [Matrix.smul_apply, hM p q h, smul_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `h1 : SP k r l p j`. Distinguish the cases in `h2 : SP k r l j q`.

It suffices to derive a contradiction. Unfold `SP at h1 h2`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hN j q h2, mul_zero]`.

Rewrite using `[hM p j h1, zero_mul]`.
-/
lemma mul_apply_S {l : Fin r} {M N : Mx k r} (hM : InS k r l M) (hN : InS k r l N)
    (p q : Fin (2 * r + k + 1)) (h : ¬ (p.val = l.val ∧ q.val = 2 * r + k - l.val)) :
    (M * N) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h1 : SP k r l p j
  · by_cases h2 : SP k r l j q
    · exfalso
      unfold SP at h1 h2
      have := l.isLt
      omega
    · rw [hN j q h2, mul_zero]
  · rw [hM p j h1, zero_mul]

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `h1 : p.val = l.val ∧ j.val = 2 * r + k - l.val`.

Establish `h2 : ¬ SP k r l j q`. Unfold `SP`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hY j q h2, mul_zero]`.

Rewrite using `[mul_apply_S hY hY p j h1, zero_mul]`.
-/
lemma cube_S {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) : Y * Y * Y = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h1 : p.val = l.val ∧ j.val = 2 * r + k - l.val
  · have h2 : ¬ SP k r l j q := by
      unfold SP
      have := l.isLt
      omega
    rw [hY j q h2, mul_zero]
  · rw [mul_apply_S hY hY p j h1, zero_mul]

/- English proof (translation)
Establish `h3 : ∀ n, 3 ≤ n → Y ^ n = 0`. Introduce `n hn`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Rewrite using `[pow_add, pow_three', cube_S hY, zero_mul]`. Establish `hz : ∀ n ∉ Finset.range 3, ((n.factorial : ℂ))⁻¹ • Y ^ n = 0`.

Introduce `n hn`. Rewrite `hn` using `[Finset.mem_range, not_lt]`. Rewrite using `[h3 n hn, smul_zero]`. Rewrite using `[NormedSpace.exp_eq_tsum (𝕂 := ℂ)]`. Simplify using `only`.

Rewrite using `[tsum_eq_sum hz]`. Simplify using `[Finset.sum_range_succ, Nat.factorial, sq, one_div]`.
-/
lemma exp_S {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) :
    NormedSpace.exp Y = 1 + Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3 : ∀ n, 3 ≤ n → Y ^ n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_three', cube_S hY, zero_mul]
  have hz : ∀ n ∉ Finset.range 3, ((n.factorial : ℂ))⁻¹ • Y ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [h3 n hn, smul_zero]
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  dsimp only
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ, Nat.factorial, sq, one_div]

/- English proof (translation)
Rewrite using `[Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, hY i j h1, mul_apply_S hY hY i j h2, smul_zero, add_zero, add_zero]`.
-/
private lemma gent_lemma {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) (i j : Fin (2 * r + k + 1))
    (h1 : ¬ SP k r l i j) (h2 : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) :
    (1 + Y + (1 / 2 : ℂ) • (Y * Y)) i j = (1 : Mx k r) i j := by
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, hY i j h1, mul_apply_S hY hY i j h2,
    smul_zero, add_zero, add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
private lemma mulVec_bvec_lemma_2 (M : Mx k r) (q : Fin (2 * r + k + 1)) :
    M *ᵥ bvec q = fun p => M p q := by
  funext p
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Establish `hl` using `l.isLt`. Use `⟨⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩, hU, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `ha` using `a.isLt`. Rewrite using `[gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]`. Conclude with `Matrix.one_apply`.

Rewrite using `[gent_lemma hY _ _ (by unfold SP; omega) (by omega)]`. Conclude with `Matrix.one_apply`. Establish `ha' : a.val < l.val` using `ha`. Establish `ha2` using `a.isLt`. Rewrite using `[mulVec_bvec_lemma_2]`.

Use function extensionality and compare the values at `p`. Rewrite using `[gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]`. Simplify using `[bvec, Pi.single_apply, Matrix.one_apply]`. Establish `ha' : a.val < l.val` using `ha`. Establish `ha2` using `a.isLt`.

Rewrite using `[mulVec_bvec_lemma_2]`. Use function extensionality and compare the values at `p`. Rewrite using `[gent_lemma hY _ _ (by unfold SP; simp only [esI_val]; omega) (by simp only [esI_val]; omega)]`. Simplify using `[bvec, Pi.single_apply, Matrix.one_apply]`.
-/
lemma memN_S {l : Fin r} {Y : Mx k r} (hY : InS k r l Y)
    (hU : 1 + Y + (1 / 2 : ℂ) • (Y * Y) ∈ UH (Hpk k r)) :
    1 + Y + (1 / 2 : ℂ) • (Y * Y) ∈ Nlev k r l.castSucc := by
  have hl := l.isLt
  refine ⟨⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩, hU, fun a ha => ⟨?_, ?_⟩⟩
  · have ha := a.isLt
    rw [gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]
    exact Matrix.one_apply
  · rw [gent_lemma hY _ _ (by unfold SP; omega) (by omega)]
    exact Matrix.one_apply
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    rw [mulVec_bvec_lemma_2]
    funext p
    rw [gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    rw [mulVec_bvec_lemma_2]
    funext p
    rw [gent_lemma hY _ _ (by unfold SP; simp only [esI_val]; omega) (by simp only [esI_val]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]

/- English proof (translation)
Unfold `ell`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Matrix.add_mulVec]`.
-/
lemma ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    ell k r z (A + B) = ell k r z A + ell k r z B := by
  unfold ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.add_mulVec]

/- English proof (translation)
Unfold `ell`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Matrix.smul_mulVec]`.
-/
lemma ell_smul (z : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (A : Mx k r) :
    ell k r z (s • A) = s * ell k r z A := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.smul_mulVec]

/- English proof (translation)
Unfold `ell`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Matrix.sub_mulVec]`.
-/
lemma ell_sub (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    ell k r z (A - B) = ell k r z A - ell k r z B := by
  unfold ell
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.sub_mulVec]

/- English proof (translation)
Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Use `split_ifs with h`. Apply `Matrix.one_apply_ne` to reduce the goal to its premises.

Introduce `he`. Use `congrArg Fin.val he` as an intermediate fact. Simplify using `only [eI_val] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.one_mulVec]`.

Conclude with `hz _ (Or.inl a.isLt)`.
-/
lemma ell_one (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : ell k r z 1 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro he
    have := congrArg Fin.val he
    simp only [eI_val] at this
    omega
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

/- English proof (translation)
Establish `hl` using `l.isLt`. Unfold `ell`. Rewrite using `[Finset.sum_eq_single l]`. Distinguish the cases in `h : l.val + 1 < r`. Establish `h' : (Fin.succ l).val < r` using `by simpa using h`.

Rewrite using `[dif_pos h]`. Simplify using `only [fvec, dif_pos h', mulVec_bvec_lemma_2]`. Both sides reduce to the same expression. Establish `h' : ¬ (Fin.succ l).val < r` using `by simpa using h`. Rewrite using `[dif_neg h]`.

Simplify using `only [fvec, dif_neg h']`. Introduce `a _ hal`. Establish `hal' : a.val ≠ l.val` using `fun e => hal (Fin.ext e)`. Establish `ha` using `a.isLt`. Use `split_ifs with h`.

Apply `hM` to reduce the goal to its premises. Unfold `SP`. Simplify using `only [eI_val]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.mulVec, dotProduct]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Distinguish the cases in `hq : SP k r l (eI k r a) q`. Establish `hq' : q.val = 2 * r + k - l.val`. Unfold `SP at hq`.

Simplify using `only [eI_val] at hq`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hz q (Or.inr (by omega)), mul_zero]`. Rewrite using `[hM _ _ hq, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma ell_S {l : Fin r} {M : Mx k r} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hM : InS k r l M) : ell k r z M = (M *ᵥ fvec k r z l.succ) (eI k r l) := by
  have hl := l.isLt
  unfold ell
  rw [Finset.sum_eq_single l]
  · by_cases h : l.val + 1 < r
    · have h' : (Fin.succ l).val < r := by simpa using h
      rw [dif_pos h]
      simp only [fvec, dif_pos h', mulVec_bvec_lemma_2]
      rfl
    · have h' : ¬ (Fin.succ l).val < r := by simpa using h
      rw [dif_neg h]
      simp only [fvec, dif_neg h']
  · intro a _ hal
    have hal' : a.val ≠ l.val := fun e => hal (Fin.ext e)
    have ha := a.isLt
    split_ifs with h
    · apply hM
      unfold SP
      simp only [eI_val]
      omega
    · simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : SP k r l (eI k r a) q
      · have hq' : q.val = 2 * r + k - l.val := by
          unfold SP at hq
          simp only [eI_val] at hq
          omega
        rw [hz q (Or.inr (by omega)), mul_zero]
      · rw [hM _ _ hq, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
