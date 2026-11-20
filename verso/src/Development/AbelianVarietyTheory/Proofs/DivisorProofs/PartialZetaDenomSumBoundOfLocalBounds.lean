import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds

/- English proof (translation)
Introduce `F _ _ hCE k z hk h16 hloc`. Use `set f := finrank ℚ F with hf`. Use `set X := f * k with hX`. Establish `h2f : 2 * f ≤ X` using `by rw [hX, mul_comm 2 f]; exact Nat.mul_le_mul_left f hk`. Establish `hvan : ∀ l : ℕ, l.Prime → X + 2 ≤ l → cE z l = 0`.

Introduce `l hl hlX`. Establish `hl2 : l ≠ 2` using `by omega`. Establish `hv : padicValNat l 2 = 0` using `padicValNat.eq_zero_of_not_dvd (fun h => by`. Use `Nat.le_of_dvd (by norm_num) h; omega)` as an intermediate fact. Establish `hm : Formalism.PairingDivisionLocalBalance.mE l X = 0`.

Unfold `Formalism.PairingDivisionLocalBalance.mE`. Rewrite using `[if_neg hl2, if_neg]`. Introduce `hd`. Use `Nat.le_of_dvd (by omega) hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `hloc l hl` as an intermediate fact. Rewrite `this` using `[hv, hm]`. Simplify using `using this`. Use `set S : Finset Nat.Primes := (Finset.range (X + 2)).subtype Nat.Prime with hS`. Establish `hsupp : (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)) ⊆ (S : Set Nat.Primes)`.

Introduce `l hl`. Simplify using `only [Function.mem_support] at hl`. Rewrite using `[Finset.mem_coe, hS]`. Use `(Finset.mem_subtype (p := Nat.Prime) (a := (l : {p : ℕ // p.Prime}))).2 (Finset.mem_range.2 ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Apply `hl` to reduce the goal to its premises. Rewrite using `[hvan l l.2 (by omega)]`. Simplify using the standard rewrite rules. Use `⟨S.finite_toSet.subset hsupp, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp]`.

Establish `hsub : ∑ l ∈ S, (cE z l : ℝ) * Real.log (l : ℕ) = ∑ l ∈ (Finset.range (X + 2)).filter Nat.Prime, (cE z l : ℝ) * Real.log l` using `Finset.sum_subtype_eq_sum_filter (f := fun l : ℕ => (cE z l : ℝ) * Real.log l) (s := Finset.range (X + 2))`. Rewrite using `[hsub]`. Use `le_trans (Finset.sum_le_sum fun l hl => ?_) (hCE f X _ h16 h2f (fun l hl => (Finset.mem_filter.1 hl).2))` and prove the remaining obligations. Establish `hlp` using `(Finset.mem_filter.1 hl).2`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast hloc l hlp) (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))`.
-/
theorem sumBound_of_local : ∀ {F : Type} [Field F] [NumberField F], Formalism.PairingDivisionLocalBalance.CESum → ∀ (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ), 2 ≤ k → 16 ≤ finrank ℚ F * k →
    (∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) → SumBound k z := by
  intro F _ _ hCE k z hk h16 hloc
  set f := finrank ℚ F with hf
  set X := f * k with hX
  have h2f : 2 * f ≤ X := by rw [hX, mul_comm 2 f]; exact Nat.mul_le_mul_left f hk

  have hvan : ∀ l : ℕ, l.Prime → X + 2 ≤ l → cE z l = 0 := by
    intro l hl hlX
    have hl2 : l ≠ 2 := by omega
    have hv : padicValNat l 2 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    have hm : Formalism.PairingDivisionLocalBalance.mE l X = 0 := by
      unfold Formalism.PairingDivisionLocalBalance.mE
      rw [if_neg hl2, if_neg]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have := hloc l hl
    rw [hv, hm] at this
    simpa using this
  set S : Finset Nat.Primes := (Finset.range (X + 2)).subtype Nat.Prime with hS
  have hsupp : (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)) ⊆ (S : Set Nat.Primes) := by
    intro l hl
    simp only [Function.mem_support] at hl
    rw [Finset.mem_coe, hS]
    refine (Finset.mem_subtype (p := Nat.Prime) (a := (l : {p : ℕ // p.Prime}))).2 (Finset.mem_range.2 ?_)
    by_contra hlt
    apply hl
    rw [hvan l l.2 (by omega)]
    simp
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hsub : ∑ l ∈ S, (cE z l : ℝ) * Real.log (l : ℕ) =
      ∑ l ∈ (Finset.range (X + 2)).filter Nat.Prime, (cE z l : ℝ) * Real.log l :=
    Finset.sum_subtype_eq_sum_filter (f := fun l : ℕ => (cE z l : ℝ) * Real.log l) (s := Finset.range (X + 2))
  rw [hsub]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (hCE f X _ h16 h2f (fun l hl => (Finset.mem_filter.1 hl).2))
  have hlp := (Finset.mem_filter.1 hl).2
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hloc l hlp)
    (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))

end GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds
