import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansionsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Establish `hM' : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem laurent_exp_shift (M : ℕ) (hM : 0 < M) (w : ℕ) (k : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * ((k - (w * M : ℕ) : ℤ) : ℂ) * τ / M) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/- English proof (translation)
The claim follows from `QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩`.
-/
theorem laurent_qAll_int (E : Subring ℂ) (M : ℕ) (hM : 0 < M) (f : ℍ → ℂ) (c : ℕ → ℤ)
    (h : HasQ 1 f fun n => (c n : ℂ)) : QAll (· ∈ E) M f :=
  QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩

/- English proof (translation)
Introduce `E M φ hM`. Take `⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩` from `GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions`. Take `⟨-, -, -, hmul, hpow, -⟩` from `GlobalTheory.QFam.QAllSubring.ring_closed E M hM`. Establish `hqD` using `laurent_qAll_int E M hM _ cD hD`. Establish `hqI` using `laurent_qAll_int E M hM _ cI hI`.

Establish `hDD0 : ∀ τ : ℍ, DD τ ≠ 0` using `ReciprocityTheory.ChartRestriction.L1.DD_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Take `⟨b, hb, hbE⟩` from `hmul _ _ (hpow _ w hqI) hw`. Set `g : ℕ → ℤ` to `fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)`.

Establish `hginj : Function.Injective g` using `fun a b h => by simpa [g] using h`. Set `c : ℤ → ℂ` to `fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0`. Use `⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩` and prove the remaining obligations. Simplify using `only [c] split_ifs`. Conclude with `hbE _`.

Conclude with `E.zero_mem`. Simplify using `only [c]`. Rewrite using `[if_neg (not_le.mpr hn)]`. Rewrite using `[← hginj.hasSum_iff]`. Establish `h1` using `(hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹`.

Establish `hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ * ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ`. Rewrite using `[div_pow]`. Clear denominators, using `[pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))), pow_ne_zero w (hDD0 τ)]` for the nonvanishing conditions. Rewrite `h1` using `[hφ]`. Establish `key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ * (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) = (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g`.

Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, g, c]`. Rewrite using `[if_pos (by omega)]`. Establish `hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k` using `by omega`. Rewrite using `[hk]`.

Use `laurent_exp_shift M hM w k τ` as an intermediate fact. Rewrite using `[← Int.cast_natCast k, ← this]`. Clear denominators, using `[pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]` for the nonvanishing conditions. Rewrite `h1` using `[key]`. Conclude with `h1`.

Introduce `n hn`. Establish `: ¬ (-((w * M : ℕ) : ℤ) ≤ n)` using `fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by`. Simplify using `only [g]`. Use the proof step `omega⟩`. Simplify using `only [c]`.

Rewrite using `[if_neg this, zero_mul]`. Introduce and unpack `⟨c, n₀, hcE, hc0, hs⟩`. Use `⟨(-n₀).toNat, ?_⟩` and prove the remaining obligations. Use `set w := (-n₀).toNat with hw`. Set `g : ℕ → ℤ` to `fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)`.

Establish `hginj : Function.Injective g` using `fun a b h => by simpa [g] using h`. Establish `hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ)`. Establish `: w ≤ w * M` using `Nat.le_mul_of_pos_right w hM`. Conclude with `this` after adjusting the coercions. Establish `hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k)`.

Introduce `τ`. Establish `h1` using `(hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)`. Rewrite `h1` using `[← hginj.hasSum_iff]`. Establish `key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g = fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M)`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp, g]`. Rewrite using `[mul_left_comm, laurent_exp_shift M hM w k τ]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[key]`.

Conclude with `h1`. Introduce `n hn`. Establish `: n < n₀`. Assume the negation of the conclusion as `hh`. Conclude with `hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩`.

Simplify using `[hc0 n this]`. Establish `hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ` using `⟨_, hq, fun k => hcE _⟩`. Establish `h2` using `hmul _ _ (hpow _ w hqD) hqE`. Establish `key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w * (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ`. Use function extensionality and compare the values at `τ`.

Rewrite using `[div_pow]`. Clear denominators, using `[pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]` for the nonvanishing conditions. Rewrite `h2` using `[key]`. Conclude with `h2`.
-/
theorem laurent_iff : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  intro E M φ hM
  obtain ⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  obtain ⟨-, -, -, hmul, hpow, -⟩ := GlobalTheory.QFam.QAllSubring.ring_closed E M hM
  have hqD := laurent_qAll_int E M hM _ cD hD
  have hqI := laurent_qAll_int E M hM _ cI hI
  have hDD0 : ∀ τ : ℍ, DD τ ≠ 0 := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, hbE⟩ := hmul _ _ (hpow _ w hqI) hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    let c : ℤ → ℂ := fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0
    refine ⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩
    · simp only [c]
      split_ifs
      · exact hbE _
      · exact E.zero_mem
    · simp only [c]
      rw [if_neg (not_le.mpr hn)]
    · rw [← hginj.hasSum_iff]
      · have h1 := (hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹
        have hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ := by
          rw [div_pow]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))),
            pow_ne_zero w (hDD0 τ)]
        rw [hφ] at h1
        have key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) =
            (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g := by
          funext k
          simp only [Function.comp, g, c]
          rw [if_pos (by omega)]
          have hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k := by omega
          rw [hk]
          have := laurent_exp_shift M hM w k τ
          rw [← Int.cast_natCast k, ← this]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
        rw [key] at h1
        exact h1
      · intro n hn
        have : ¬ (-((w * M : ℕ) : ℤ) ≤ n) := fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by
          simp only [g]; omega⟩
        simp only [c]
        rw [if_neg this, zero_mul]
  · rintro ⟨c, n₀, hcE, hc0, hs⟩
    refine ⟨(-n₀).toNat, ?_⟩
    set w := (-n₀).toNat with hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    have hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ) := by
      have : w ≤ w * M := Nat.le_mul_of_pos_right w hM
      exact_mod_cast this
    have hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k) := by
      intro τ
      have h1 := (hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)
      rw [← hginj.hasSum_iff] at h1
      · have key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g =
            fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M) := by
          funext k
          simp only [Function.comp, g]
          rw [mul_left_comm, laurent_exp_shift M hM w k τ]
          push_cast
          rfl
        rw [key] at h1
        exact h1
      · intro n hn
        have : n < n₀ := by
          by_contra hh
          exact hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩
        simp [hc0 n this]
    have hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ :=
      ⟨_, hq, fun k => hcE _⟩
    have h2 := hmul _ _ (hpow _ w hqD) hqE
    have key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w *
        (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ := by
      funext τ
      rw [div_pow]
      field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
    rw [key] at h2
    exact h2

end GlobalTheory.FN
