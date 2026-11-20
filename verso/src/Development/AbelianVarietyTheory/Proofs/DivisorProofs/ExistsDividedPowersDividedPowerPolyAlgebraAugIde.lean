import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

/- English proof (translation)
Establish `h1` using `Nat.uniformBell_mul_eq n hN`. Establish `h2` using `Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)`. Establish `h3` using `Nat.uniformBell_mul_eq m hn`. Establish `h4` using `Nat.uniformBell_mul_eq (m * n) hN`. Establish `hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n)` using `by positivity`.

Use `Nat.eq_of_mul_eq_mul_right hpos ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, h4]`. Use `_ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring`.
-/
theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc n.uniformBell N ^ m * m.uniformBell (n * N) * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n))
      = m.uniformBell (n * N) * (n.uniformBell N * N.factorial ^ n * n.factorial) ^ m * m.factorial := by ring
    _ = (m * (n * N)).factorial := by rw [h1, h2]
    _ = ((m * n) * N).factorial := by rw [Nat.mul_assoc]
    _ = (m * n).uniformBell N * N.factorial ^ (m * n) * (m.uniformBell n * n.factorial ^ m * m.factorial) := by
      rw [h3, h4]
    _ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring

/- English proof (translation)
Introduce `B _ Q`. Take `⟨γ, hγ, he⟩` from `GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal B Q`. Establish `hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x`. Introduce and unpack `_ ⟨k, rfl⟩ m n hn`. Take `⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1` from `⟨n * (k + 1) - 1, by`.

Establish `: 0 < n * (k + 1)` using `Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos`. Use the proof step `omega⟩`. Establish `hmem : Q.e (n * (k + 1)) ∈ Q.aug` using `hj ▸ Q.e_succ_mem_aug j`. Establish `key` using `congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)`. Move the coercions through the operations in `at key`.

Rewrite using `[he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]`. Take the linear combination `key * Q.e (m * n * (k + 1))`. Take `⟨δ, hδ⟩` from `GlobalTheory.T.exists_dividedPowers_of_comp_on_generators Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp`. Use `⟨δ, fun n ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hδ]`.

Use `he n 0` as an intermediate fact. Simplify `this` using `[Nat.uniformBell_one_right]`.
-/
theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨γ, hγ, he⟩ := GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal B Q
  have hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 →
      γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x := by
    rintro _ ⟨k, rfl⟩ m n hn
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 := ⟨n * (k + 1) - 1, by
      have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
      omega⟩
    have hmem : Q.e (n * (k + 1)) ∈ Q.aug := hj ▸ Q.e_succ_mem_aug j
    have key := congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)
    push_cast at key
    rw [he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]
    linear_combination key * Q.e (m * n * (k + 1))
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp
  refine ⟨δ, fun n ↦ ?_⟩
  rw [hδ]
  have := he n 0
  simpa [Nat.uniformBell_one_right] using this

end GlobalTheory.PDA
