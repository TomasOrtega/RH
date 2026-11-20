import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQDerivationCompletionZpStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationExtendPadicLaurentToClosureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationEqZeroOfIsAlgebraicOverPadicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeNatCastCompletedLaurentRingOfPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqPrimePowMulNotDvdCompletedLaurentStatement
open GlobalTheory.K5

namespace GlobalTheory.K5.NotPow

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_qDerivation_completion_Zp p`.
-/
theorem exists_derivation_fix_q_kill_padicInt (p : ℕ) [Fact p.Prime] : ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := GlobalTheory.T.exists_qDerivation_completion_Zp p

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure p Ω h D`.
-/
theorem derExt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (D : Derivation ℤ (O0 p) (O0 p)) :
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) :=
  GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure p Ω h D

/- English proof (translation)
The claim follows from `GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers p Ω h E hE`.
-/
theorem derAlg (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (E : Derivation ℤ Ω Ω) (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) :
    ∀ x : Ω, IsAlgZp p x → E x = 0 := GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers p Ω h E hE

/- English proof (translation)
Introduce `b hb`. Take `⟨g₁, hg₁, hy⟩` from `GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers p Ω h b hb`. Take `⟨n, a, f, g₂, ha, hli, hg₂, he⟩` from `GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers p Ω h _ hy`. Use `⟨n, a, f, g₂ * g₁, ha, hli, mul_ne_zero hg₂ hg₁, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc, he]`.
-/
theorem repr (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω) :
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * b = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro b hb
  obtain ⟨g₁, hg₁, hy⟩ := GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers p Ω h b hb
  obtain ⟨n, a, f, g₂, ha, hli, hg₂, he⟩ := GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers p Ω h _ hy
  refine ⟨n, a, f, g₂ * g₁, ha, hli, mul_ne_zero hg₂ hg₁, ?_⟩
  rw [map_mul, mul_assoc, he]

/- English proof (translation)
The claim follows from `GlobalTheory.T.prime_natCast_completed_laurent_ring p`.
-/
theorem primeP (p : ℕ) [Fact p.Prime] : Prime (p : O0 p) := GlobalTheory.T.prime_natCast_completed_laurent_ring p

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 p`.
-/
theorem splitP (p : ℕ) [Fact p.Prime] : ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 p

/- English proof (translation)
Introduce `heq`. Take `⟨a, f0, rfl, hf0⟩` from `splitP p f hf`. Take `⟨c, g0, rfl, hg0⟩` from `splitP p g hg`. Establish `hD : ∀ (k : ℕ) (y : O0 p), D ((p : O0 p) ^ k * y) = (p : O0 p) ^ k * D y`. Introduce `k y`.

Rewrite using `[Derivation.leibniz, Derivation.leibniz_pow]`. Establish `: D (p : O0 p) = 0`. Use `D.map_algebraMap (p : ℤ)` as an intermediate fact. Simplify using `using this`. Simplify using `[this]`.

Rewrite `heq` using `[hD, hD]`. Establish `hp0 : (p : O0 p) ≠ 0` using `(primeP p).ne_zero`. Establish `h2 : (p : O0 p) ^ (c + a) * ((p : O0 p) * (g0 * D f0 - f0 * D g0)) = (p : O0 p) ^ (c + a) * (g0 * f0)`. Rewrite using `[pow_add]`. Take the linear combination `heq`.

Establish `h3` using `mul_left_cancel₀ (pow_ne_zero _ hp0) h2`. Establish `h4 : (p : O0 p) ∣ g0 * f0` using `⟨_, h3.symm⟩`. Break down `(primeP p).dvd_or_dvd h4 with h | h` into its components or cases. Conclude with `hg0 h`. Conclude with `hf0 h`.
-/
theorem not_eigen (p : ℕ) [Fact p.Prime] (D : Derivation ℤ (O0 p) (O0 p)) (f g : O0 p)
    (hf : f ≠ 0) (hg : g ≠ 0) : (p : O0 p) * (g * D f - f * D g) ≠ g * f := by
  intro heq
  obtain ⟨a, f0, rfl, hf0⟩ := splitP p f hf
  obtain ⟨c, g0, rfl, hg0⟩ := splitP p g hg
  have hD : ∀ (k : ℕ) (y : O0 p), D ((p : O0 p) ^ k * y) = (p : O0 p) ^ k * D y := by
    intro k y
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    have : D (p : O0 p) = 0 := by
      have := D.map_algebraMap (p : ℤ)
      simpa using this
    simp [this]
  rw [hD, hD] at heq
  have hp0 : (p : O0 p) ≠ 0 := (primeP p).ne_zero
  have h2 : (p : O0 p) ^ (c + a) * ((p : O0 p) * (g0 * D f0 - f0 * D g0)) =
      (p : O0 p) ^ (c + a) * (g0 * f0) := by
    rw [pow_add]; linear_combination heq
  have h3 := mul_left_cancel₀ (pow_ne_zero _ hp0) h2
  have h4 : (p : O0 p) ∣ g0 * f0 := ⟨_, h3.symm⟩
  rcases (primeP p).dvd_or_dvd h4 with h | h
  · exact hg0 h
  · exact hf0 h

/- English proof (translation)
Introduce `p _ Ω _ _ h b hb hbp`. Establish `hp : p.Prime` using `Fact.out`. Use `haveI : CharZero Ω := Basic.charZero_of_isClo h`. Take `⟨D, hDq, hDr⟩` from `exists_derivation_fix_q_kill_padicInt p`. Take `⟨E, hE⟩` from `derExt p Ω h D`.

Establish `hEr : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0`. Introduce `r`. Rewrite using `[hE, hDr, map_zero]`. Establish `hEa` using `derAlg p Ω h E hEr`. Establish `hq0 : algebraMap (O0 p) Ω (qO p) ≠ 0` using `((Basic.isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero`.

Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Rewrite `hbp` using `[zero_pow hp.ne_zero]`. Conclude with `hq0 hbp.symm`. Establish `hpΩ : (p : Ω) ≠ 0` using `by exact_mod_cast hp.ne_zero`.

Establish `hEb : (p : Ω) * E b = b`. Establish `h1` using `congrArg E hbp`. Rewrite `h1` using `[Derivation.leibniz_pow, hE, hDq, ← hbp]`. Establish `h2 : b ^ (p - 1) * ((p : Ω) * E b) = b ^ (p - 1) * b`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hp.one_lt.le]`.

Rewrite `h1` using `[nsmul_eq_mul, smul_eq_mul]`. Take the linear combination `h1`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ hb0) h2`. Take `⟨n, a, f, g, ha, hli, hg, hrep⟩` from `repr p Ω h b hb`. Use `set φ := algebraMap (O0 p) Ω with hφ`.

Establish `hEsum` using `congrArg E hrep`. Rewrite `hEsum` using `[Derivation.leibniz, map_sum]`. Simplify using `only [Derivation.leibniz, hEa _ (ha _), smul_zero, zero_add, smul_eq_mul, hE, mul_zero] at hEsum`. Set `c : Fin n → O0 p` to `fun i => g * f i + (p : O0 p) * D g * f i - (p : O0 p) * g * D (f i)`. Establish `hc : ∑ i, c i • a i = 0`.

Simplify using `only [c, Algebra.smul_def, ← hφ, map_add, map_sub, map_mul, map_natCast]`. Establish `e1 : ∑ i, (φ g * φ (f i) + (p : Ω) * φ (D g) * φ (f i) - (p : Ω) * φ g * φ (D (f i))) * a i = (φ g + (p : Ω) * φ (D g)) * ∑ i, φ (f i) * a i - (p : Ω) * φ g * ∑ i, a i * φ (D (f i))`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations. Rewrite using `[e1, ← hrep, ← hEsum]`.

Take the linear combination `-(φ g * φ g) * hEb`. Establish `hc'` using `(Fintype.linearIndependent_iff.1 hli) c hc`. Establish `: ∃ i, f i ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Apply `hb0` to reduce the goal to its premises. Establish `: φ g * b = 0` using `by rw [hrep]; simp [hall]`. Break down `mul_eq_zero.1 this with h0 | h0` into its components or cases. Conclude with `absurd (h.inj (by rw [h0, map_zero])) hg`. Conclude with `h0`.

Take `⟨i, hi⟩` from `this`. Apply `not_eigen p D (f i) g hi hg` to reduce the goal to its premises. Use `hc' i` as an intermediate fact. Simplify using `only [c] at this`. Take the linear combination `-this`.
-/
theorem q_not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  intro p _ Ω _ _ h b hb hbp
  have hp : p.Prime := Fact.out
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  obtain ⟨D, hDq, hDr⟩ := exists_derivation_fix_q_kill_padicInt p
  obtain ⟨E, hE⟩ := derExt p Ω h D
  have hEr : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0 := by
    intro r; rw [hE, hDr, map_zero]
  have hEa := derAlg p Ω h E hEr
  have hq0 : algebraMap (O0 p) Ω (qO p) ≠ 0 :=
    ((Basic.isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hbp; exact hq0 hbp.symm
  have hpΩ : (p : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hEb : (p : Ω) * E b = b := by
    have h1 := congrArg E hbp
    rw [Derivation.leibniz_pow, hE, hDq, ← hbp] at h1
    have h2 : b ^ (p - 1) * ((p : Ω) * E b) = b ^ (p - 1) * b := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
      rw [nsmul_eq_mul, smul_eq_mul] at h1
      linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero _ hb0) h2
  obtain ⟨n, a, f, g, ha, hli, hg, hrep⟩ := repr p Ω h b hb
  set φ := algebraMap (O0 p) Ω with hφ
  have hEsum := congrArg E hrep
  rw [Derivation.leibniz, map_sum] at hEsum
  simp only [Derivation.leibniz, hEa _ (ha _), smul_zero, zero_add, smul_eq_mul, hE, mul_zero] at hEsum
  let c : Fin n → O0 p := fun i => g * f i + (p : O0 p) * D g * f i - (p : O0 p) * g * D (f i)

  have hc : ∑ i, c i • a i = 0 := by
    simp only [c, Algebra.smul_def, ← hφ, map_add, map_sub, map_mul, map_natCast]
    have e1 : ∑ i, (φ g * φ (f i) + (p : Ω) * φ (D g) * φ (f i) - (p : Ω) * φ g * φ (D (f i))) * a i
        = (φ g + (p : Ω) * φ (D g)) * ∑ i, φ (f i) * a i - (p : Ω) * φ g * ∑ i, a i * φ (D (f i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, ← hrep, ← hEsum]
    linear_combination -(φ g * φ g) * hEb
  have hc' := (Fintype.linearIndependent_iff.1 hli) c hc
  have : ∃ i, f i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hb0
    have : φ g * b = 0 := by rw [hrep]; simp [hall]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (h.inj (by rw [h0, map_zero])) hg
    · exact h0
  obtain ⟨i, hi⟩ := this
  apply not_eigen p D (f i) g hi hg
  have := hc' i
  simp only [c] at this
  linear_combination -this

end GlobalTheory.K5.NotPow
