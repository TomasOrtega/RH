import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertCofinite

open Matrix TensorProduct Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

/- English proof (translation)
Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => exact absurd rfl hn`. Consider the case `one => exact ⟨_, eps_mem P, by simp⟩`. Consider the case `prime p hp`. Take `⟨s, hs, e⟩` from `eps_dvd (E := D.host.E) P hp (h p hp dvd_rfl) 1`.

Conclude with `⟨s, hs, by simpa using e⟩`. Consider the case `mul a b ha hb`. Take `⟨s, hs, es⟩` from `ha (left_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_right _)`. Take `⟨t, ht, et⟩` from `hb (right_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_left _)`. Use `⟨s * t, mul_mem hs ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[← eps_idem P]`. Use `conv_lhs => enter [1]`. Rewrite using `[es]`. Rewrite using `[et]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_dvd_nat (D : D7) (P : ℕ → Prop) (n : ℕ) (hn : n ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ n → ¬ P q) :
    ∃ t ∈ OhE D, eps D.host.E P = (n : AE D) * t := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => exact ⟨_, eps_mem P, by simp⟩
  | prime p hp =>
    obtain ⟨s, hs, e⟩ := eps_dvd (E := D.host.E) P hp (h p hp dvd_rfl) 1
    exact ⟨s, hs, by simpa using e⟩
  | mul a b ha hb =>
    obtain ⟨s, hs, es⟩ := ha (left_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_right _)
    obtain ⟨t, ht, et⟩ := hb (right_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_left _)
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [← eps_idem P]
    conv_lhs => enter [1]; rw [es]
    rw [et]
    push_cast
    ring

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `levelaf_denom (F := ℚ) y`. Take `⟨z, rfl⟩ : ∃ z : ℤ, d = z` from `⟨Rat.ringOfIntegersEquiv d, by`. Apply `Rat.ringOfIntegersEquiv.injective` to reduce the goal to its premises. Use the proof step `simp⟩`. Establish `hz : z.natAbs ≠ 0` using `by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]`.

Establish `hC : levelafC (F` using `ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by`. Rewrite using `[levelafC, map_intCast]`. Conclude with `map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z`. Use `⟨z.natAbs, Nat.pos_of_ne_zero hz, ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[hC]`.

Break down `Int.natAbs_eq z with e | e` into its components or cases. Rewrite `hd` using `[e]`. Simplify `hd` using `[OhE]`. Rewrite `hd` using `[e]`. Use `neg_mem hd` as an intermediate fact.

Simplify `this` using `[OhE]`.
-/
theorem exists_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (F := ℚ) y
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, d = z := ⟨Rat.ringOfIntegersEquiv d, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have hz : z.natAbs ≠ 0 := by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]
  have hC : levelafC (F := ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by
    rw [levelafC, map_intCast]
    exact map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z
  refine ⟨z.natAbs, Nat.pos_of_ne_zero hz, ?_⟩
  rw [hC] at hd
  rcases Int.natAbs_eq z with e | e
  · rw [e] at hd; simpa [OhE] using hd
  · rw [e] at hd
    have := neg_mem hd
    simpa [OhE] using this

/- English proof (translation)
Establish `hex` using `exists_denom D y`. Take `⟨h0, h1⟩` from `Nat.find_spec hex`. Use `⟨Nat.find hex, h0, h1, fun q hq hd hz => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hc, s, hs, e⟩` from `hz 0`. Rewrite `e` using `[pow_zero, one_mul]`.

Establish `hm' : (m : AE D) * y ∈ OhE D` using `e ▸ hs`. Establish `hg : ((Nat.gcd (Nat.find hex) m : ℕ) : AE D) * y ∈ OhE D`. Use `congrArg (Int.cast : ℤ → AE D) (Nat.gcd_eq_gcd_ab (Nat.find hex) m)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`.

Use `add_mem (mul_mem (intCast_mem (OhE D) (Nat.gcdA (Nat.find hex) m)) h1) (mul_mem (intCast_mem (OhE D) (Nat.gcdB (Nat.find hex) m)) hm') using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left _ h0, hg⟩`. Establish `heq : Nat.gcd (Nat.find hex) m = Nat.find hex` using `le_antisymm (Nat.gcd_le_left _ h0) hle`. Establish `: q ∣ m` using `hd.trans (heq ▸ Nat.gcd_dvd_right _ _)`.

Conclude with `(Nat.Prime.coprime_iff_not_dvd hq).1 hc.symm this`.
-/
theorem exists_denom_zeroAt (D : D7) (y : AE D) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D ∧ ∀ q : ℕ, q.Prime → q ∣ n → ¬ ZeroAt D q y := by
  have hex := exists_denom D y
  obtain ⟨h0, h1⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, h1, fun q hq hd hz => ?_⟩
  obtain ⟨m, hm, hc, s, hs, e⟩ := hz 0
  rw [pow_zero, one_mul] at e
  have hm' : (m : AE D) * y ∈ OhE D := e ▸ hs
  have hg : ((Nat.gcd (Nat.find hex) m : ℕ) : AE D) * y ∈ OhE D := by
    have := congrArg (Int.cast : ℤ → AE D) (Nat.gcd_eq_gcd_ab (Nat.find hex) m)
    push_cast at this
    rw [this]
    convert add_mem (mul_mem (intCast_mem (OhE D) (Nat.gcdA (Nat.find hex) m)) h1)
      (mul_mem (intCast_mem (OhE D) (Nat.gcdB (Nat.find hex) m)) hm') using 1
    ring
  have hle := Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left _ h0, hg⟩
  have heq : Nat.gcd (Nat.find hex) m = Nat.find hex := le_antisymm (Nat.gcd_le_left _ h0) hle
  have : q ∣ m := hd.trans (heq ▸ Nat.gcd_dvd_right _ _)
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hc.symm this

/- English proof (translation)
Establish `hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) = (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D)` using `g.2`. Rewrite `hg` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Introduce `i j`. Use `⟨h i j, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.inv_eq_of_mul_eq_one_left hg]`.

Conclude with `csDual_sig_mem _ (h j i)`.
-/
theorem intG_of_entries (D : D7) {N : ℕ} (g : GA D N)
    (h : ∀ i j, ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) :
    IntG D (g : GL (Fin N) (AE D)) := by
  have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hg
  intro i j
  refine ⟨h i j, ?_⟩
  rw [Units.inv_eq_of_mul_eq_one_left hg]
  exact csDual_sig_mem _ (h j i)

/- English proof (translation)
Use `choose n h0 h1 h2 using fun ij : Fin N × Fin N => exists_denom_zeroAt D (((y : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2)`. Use `⟨Finset.univ.biUnion fun ij => (n ij).primeFactors, fun p hp => ?_, intG_of_entries D _ fun i j => ?_⟩` and prove the remaining obligations. Take `⟨ij, -, hp⟩` from `Finset.mem_biUnion.1 hp`. Establish `hq` using `Nat.prime_of_mem_primeFactors hp`. Use `⟨hq, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hi`. Conclude with `h2 ij p hq (Nat.dvd_of_mem_primeFactors hp) (hy p hq hi ij.1 ij.2)`. Take `⟨t, ht, e⟩` from `eps_dvd_nat D (fun p => p ∉ Finset.univ.biUnion fun ij => (n ij).primeFactors) (n (i, j)) (h0 _).ne' fun q hq hd hn => hn (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hq, hd, (h0 _).ne'⟩⟩)`. Use `add_mem (mul_mem ht (h1 (i, j))) (one_entry_mem (OhE D) i j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `show cutM _ _ _ i j = _`. Rewrite using `[cutM_apply, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intG_part_cofinite {D : D7} {N : ℕ} (y : GA D N) (hy : SuppInert D (y : GL (Fin N) (AE D))) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ InertQ D p) ∧
      IntG D (part D (fun p => p ∉ s) y : GL (Fin N) (AE D)) := by
  choose n h0 h1 h2 using fun ij : Fin N × Fin N => exists_denom_zeroAt D
    (((y : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2)
  refine ⟨Finset.univ.biUnion fun ij => (n ij).primeFactors, fun p hp => ?_, intG_of_entries D _ fun i j => ?_⟩
  · obtain ⟨ij, -, hp⟩ := Finset.mem_biUnion.1 hp
    have hq := Nat.prime_of_mem_primeFactors hp
    refine ⟨hq, ?_⟩
    by_contra hi
    exact h2 ij p hq (Nat.dvd_of_mem_primeFactors hp) (hy p hq hi ij.1 ij.2)
  · obtain ⟨t, ht, e⟩ := eps_dvd_nat D (fun p => p ∉ Finset.univ.biUnion fun ij => (n ij).primeFactors) (n (i, j))
      (h0 _).ne' fun q hq hd hn => hn (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Nat.mem_primeFactors.2 ⟨hq, hd, (h0 _).ne'⟩⟩)
    have := add_mem (mul_mem ht (h1 (i, j))) (one_entry_mem (OhE D) i j)
    convert this using 1
    show cutM _ _ _ i j = _
    rw [cutM_apply, e]
    ring

end GlobalTheory.InertCofinite
