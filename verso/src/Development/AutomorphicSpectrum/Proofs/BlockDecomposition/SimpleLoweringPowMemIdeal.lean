import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

def adL (F u : U n) : U n := F * u - u * F

/- English proof (translation)
Simplify using `[adL]`.
-/
theorem adL_zero (F : U n) : adL F 0 = 0 := by simp [adL]

/- English proof (translation)
Simplify using `only [adL, mul_sub, sub_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem adL_sub (F u v : U n) : adL F (u - v) = adL F u - adL F v := by
  simp only [adL, mul_sub, sub_mul]; abel

/- English proof (translation)
Simplify using `only [adL, mul_neg, neg_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem adL_neg (F u : U n) : adL F (-u) = - adL F u := by
  simp only [adL, mul_neg, neg_mul]; abel

/- English proof (translation)
The claim follows from `e_mul_sub_mul (j, i) (c, d)`.
-/
theorem adL_e (i j c d : Fin n) :
    adL (e (j, i)) (e (c, d)) =
      (if i = c then e (j, d) else 0) - (if d = j then e (c, i) else 0) :=
  e_mul_sub_mul (j, i) (c, d)

/- English proof (translation)
Take `⟨c, d⟩` from `a`. Use `show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0`. Establish `hji : j ≠ i` using `hij.symm`. Apply the tactic sequence `by_cases h1 : i = c <;> by_cases h2 : d = j`. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Simplify using `[adL_e, adL_sub, adL_neg, adL_zero, hij, hji]`. Substitute `h1` using the available equality. Simplify using `[adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]`. Substitute `h2` using the available equality.

Simplify using `[adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]`. Simplify using `[adL_e, adL_sub, adL_neg, adL_zero, h1, h2]`.
-/
theorem adL_iter_e {i j : Fin n} (hij : i ≠ j) (a : Fin n × Fin n) :
    (adL (e (j, i)))^[3] (e a) = 0 := by
  obtain ⟨c, d⟩ := a
  show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0
  have hji : j ≠ i := hij.symm
  by_cases h1 : i = c <;> by_cases h2 : d = j
  · subst h1; subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji]
  · subst h1
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]
  · subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]
  · simp [adL_e, adL_sub, adL_neg, adL_zero, h1, h2]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le' h`. Rewrite using `[pow_add, mul_assoc]`. Conclude with `mul_mem_Jp _ hw`.
-/
theorem pow_mul_mem_Jp_of_le {F w : U n} {N N' : ℕ} (h : N ≤ N') (hw : F ^ N * w ∈ Jp n) :
    F ^ N' * w ∈ Jp n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, mul_assoc]
  exact mul_mem_Jp _ hw

/- English proof (translation)
Proceed by induction on `s using Nat.strong_induction_on with`. Consider the case `_ s ih`. Introduce `r M u y hs hu hy`. Break down `M with _ | M` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite `hy`, the goal using `[pow_zero, one_mul]`. Conclude with `mul_mem_Jp u hy`. Break down `r with _ | r` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: u = 0` using `hu`.

Simplify using `[this]`. Take `⟨N₁, h₁⟩` from `ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu (by rw [← mul_assoc, ← pow_succ]; exact hy)`. Take `⟨N₂, h₂⟩` from `ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl (by rw [← Function.iterate_succ_apply]; exact hu) hy`. Use `⟨max N₁ N₂ + 1, ?_⟩` and prove the remaining obligations. Establish `key : F ^ (max N₁ N₂ + 1) * (u * y) = F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y)`.

Rewrite using `[pow_succ, ← mul_add, mul_assoc]`. Use `congr 1`. Simplify using `only [adL, sub_mul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`.

Conclude with `Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁) (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)`.
-/
theorem exists_pow_mul_mul_mem (F : U n) (s : ℕ) :
    ∀ (r M : ℕ) (u y : U n), r + M = s → (adL F)^[r] u = 0 → F ^ M * y ∈ Jp n →
      ∃ N : ℕ, F ^ N * (u * y) ∈ Jp n := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro r M u y hs hu hy
    rcases M with _ | M
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul] at hy ⊢
      exact mul_mem_Jp u hy
    rcases r with _ | r
    · refine ⟨0, ?_⟩
      have : u = 0 := hu
      simp [this]
    obtain ⟨N₁, h₁⟩ := ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu
      (by rw [← mul_assoc, ← pow_succ]; exact hy)
    obtain ⟨N₂, h₂⟩ := ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl
      (by rw [← Function.iterate_succ_apply]; exact hu) hy
    refine ⟨max N₁ N₂ + 1, ?_⟩
    have key : F ^ (max N₁ N₂ + 1) * (u * y) =
        F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y) := by
      rw [pow_succ, ← mul_add, mul_assoc]
      congr 1
      simp only [adL, sub_mul, mul_assoc]
      abel
    rw [key]
    exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)

/- English proof (translation)
Establish `hne : i ≠ j`. Introduce `h`. Rewrite `hij` using `[h]`. Use linear arithmetic over natural numbers and integers. Establish `step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) → ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n`.

Introduce `v`. Proceed by induction on `v using U.induction with`. Consider the case `halg r`. Introduce and unpack `y ⟨N, hN⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r hN`. Consider the case `hι X`. Introduce `y hy`. Take `⟨M, hM⟩` from `hy`.

Establish `hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N * ((∑ a ∈ t, X a.1 a.2 • e (n` using `n) a) * y) ∈ Jp n := by`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert a t ha ih`.

Take `⟨N₁, h₁⟩` from `ih`. Take `⟨N₂, h₂⟩` from `exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl (adL_iter_e hne a) hM`. Use `⟨max N₁ N₂, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)) (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)`.

Rewrite using `[ι_eq_sum_e]`. Conclude with `hsum Finset.univ`. Consider the case `hmul a b ha hb`. Introduce `y hy`. Rewrite using `[mul_assoc]`.

Conclude with `ha _ (hb _ hy)`. Consider the case `hadd a b ha hb`. Introduce `y hy`. Take `⟨N₁, h₁⟩` from `ha y hy`. Take `⟨N₂, h₂⟩` from `hb y hy`.

Use `⟨max N₁ N₂, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, mul_add]`. Conclude with `Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁) (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)`. Establish `h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n` using `⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩`. Simplify using `using step x 1 h1`.
-/
theorem lower_locally_nilpotent {n : ℕ} (i j : Fin n) (x : U n) (hij : (j : ℕ) = i + 1) :
    ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) →
      ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n := by
    intro v
    induction v using U.induction with
    | halg r =>
      rintro y ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
      exact Submodule.smul_mem _ r hN
    | hι X =>
      intro y hy
      obtain ⟨M, hM⟩ := hy
      have hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N *
          ((∑ a ∈ t, X a.1 a.2 • e (n := n) a) * y) ∈ Jp n := by
        intro t
        induction t using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert a t ha ih =>
          obtain ⟨N₁, h₁⟩ := ih
          obtain ⟨N₂, h₂⟩ := exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl
            (adL_iter_e hne a) hM
          refine ⟨max N₁ N₂, ?_⟩
          rw [Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂))
            (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      rw [ι_eq_sum_e]
      exact hsum Finset.univ
    | hmul a b ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb _ hy)
    | hadd a b ha hb =>
      intro y hy
      obtain ⟨N₁, h₁⟩ := ha y hy
      obtain ⟨N₂, h₂⟩ := hb y hy
      refine ⟨max N₁ N₂, ?_⟩
      rw [add_mul, mul_add]
      exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
        (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)
  have h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n :=
    ⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩
  simpa using step x 1 h1

end GlobalTheory.CompanionTheory.PresRho
