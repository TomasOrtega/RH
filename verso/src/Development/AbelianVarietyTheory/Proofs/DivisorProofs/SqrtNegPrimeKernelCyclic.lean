import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `p F L t hp _ _ D`. Establish `hsq : sqrtNegNat p ^ 2 = -(p : ℂ)` using `sqrtNegNat_sq p`. Establish `hz : ∀ (n : ℤ) (x : ℂ), x ∈ L.lattice → (n : ℂ) * x ∈ L.lattice` using `fun n x hx => by`. Simplify `L.lattice.smul_mem n hx` using `[zsmul_eq_mul]`. Establish `hpt : (p : ℂ) * t ∈ L.lattice`.

Establish `h` using `L.lattice.neg_mem (D.mul _ D.ker)`. Establish `e : -(sqrtNegNat p * (sqrtNegNat p * t)) = (p : ℂ) * t`. Take the linear combination `(-t) * hsq`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `h1 : ∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k`.

Introduce `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Assume the negation of the conclusion as `hnd`. Establish `hc : IsCoprime (p : ℤ) k` using `(Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hnd`.

Take `⟨a, b, hab⟩` from `hc`. Apply `D.notMem` to reduce the goal to its premises. Establish `h` using `L.lattice.add_mem (hz a _ hpt) (hz b _ hk)`. Establish `hab' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (k : ℂ) = 1` using `by exact_mod_cast congrArg (Int.cast (R := ℂ)) hab`. Establish `e : (a : ℂ) * ((p : ℂ) * t) + (b : ℂ) * ((k : ℂ) * t) = t`.

Take the linear combination `t * hab'`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Introduce and unpack `⟨c, rfl⟩`. Establish `h` using `hz c _ hpt`. Establish `e : (c : ℂ) * ((p : ℂ) * t) = (((p : ℤ) * c : ℤ) : ℂ) * t` using `by push_cast; ring`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hker : ∀ k : ℕ, sqrtNegNat p * ((k : ℂ) * t) ∈ L.lattice` using `fun k => by`. Establish `h` using `hz k _ D.ker`. Establish `e : ((k : ℤ) : ℂ) * (sqrtNegNat p * t) = sqrtNegNat p * ((k : ℂ) * t)` using `by push_cast; ring`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `hnot : ∀ k ∈ Finset.Ico 1 p, (k : ℂ) * t ∉ L.lattice` using `fun k hk h => by`. Rewrite `hk` using `[Finset.mem_Ico]`. Establish `h' : (p : ℤ) ∣ (k : ℤ)` using `(h1 k).mp (by exact_mod_cast h)`. Use `Nat.le_of_dvd hk.1 (Int.natCast_dvd_natCast.mp h')` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hinj : ∀ k ∈ Finset.Ico 1 p, ∀ l ∈ Finset.Ico 1 p, (k : ℂ) * t - (l : ℂ) * t ∈ L.lattice → k = l`. Introduce `k hk l hl h`. Rewrite `hk`, `hl` using `[Finset.mem_Ico]`. Establish `e : (k : ℂ) * t - (l : ℂ) * t = (((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * t` using `by push_cast; ring`. Rewrite `h` using `[e, h1]`.

Apply the tactic sequence `have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)`. Use linear arithmetic over natural numbers and integers. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hn : Complex.normSq (sqrtNegNat p) = p`. Establish `h` using `congrArg Complex.normSq hsq`.

Rewrite `h` using `[map_pow, Complex.normSq_neg, Complex.normSq_natCast, ← sq]`. Conclude with `(pow_left_inj₀ (Complex.normSq_nonneg _) hp0.le two_ne_zero).mp h`. Establish `hα : sqrtNegNat p ≠ 0` using `fun h => by`. Rewrite `hn` using `[h, map_zero]`. Conclude with `hp0.ne hn`.

Take `⟨S, hS⟩` from `kerRepsExist L _ hα D.mul`. Establish `hcard : S.card + 1 = p`. Establish `h` using `kerRepsCard L _ S hα D.mul hS`. Rewrite `h` using `[hn]`. Conclude with `h` after adjusting the coercions.

Use `choose f hfS hf using fun k (hk : k ∈ Finset.Ico 1 p) => hS.2.2 _ (hker k) (hnot k hk)`. Establish `hsurj` using `Finset.surj_on_of_inj_on_of_card_le f hfS (fun k l hk hl h => hinj k hk l hl (by`. Establish `h'` using `L.lattice.sub_mem (hf k hk) (hf l hl)`. Rewrite `h'` using `[h]`. Simplify using `using h'))`.

Use the proof step `(by rw [Nat.card_Ico]; omega)`. Establish `h3 : ∀ z, sqrtNegNat p * z ∈ L.lattice → z ∉ L.lattice → ∃ k ∈ Finset.Ico 1 p, z - (k : ℂ) * t ∈ L.lattice`. Introduce `z hz1 hz2`. Take `⟨P, hP, hzP⟩` from `hS.2.2 z hz1 hz2`. Take `⟨k, hk, rfl⟩` from `hsurj P hP`.

Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Simplify using `using L.lattice.sub_mem hzP (hf k hk)`. Use `⟨h1, fun z hz1 => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hz2 : z ∈ L.lattice`. Conclude with `⟨0, hp.pos, by simpa using hz2⟩`.

Take `⟨k, hk, h⟩` from `h3 z hz1 hz2`. Conclude with `⟨k, (Finset.mem_Ico.mp hk).2, h⟩`. Introduce `P hP`. Take `⟨k, hk, rfl⟩` from `Finset.mem_image.mp hP`. Conclude with `⟨hker k, hnot k hk⟩`.

Introduce `P hP Q hQ h`. Take `⟨k, hk, rfl⟩` from `Finset.mem_image.mp hP`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.mp hQ`. Rewrite using `[hinj k hk l hl h]`. Introduce `z hz1 hz2`.

Take `⟨k, hk, h⟩` from `h3 z hz1 hz2`. Conclude with `⟨_, Finset.mem_image_of_mem _ hk, h⟩`.
-/
theorem ker_sqrtNegNat_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  intro p F L t hp _ _ D
  have hsq : sqrtNegNat p ^ 2 = -(p : ℂ) := sqrtNegNat_sq p
  have hz : ∀ (n : ℤ) (x : ℂ), x ∈ L.lattice → (n : ℂ) * x ∈ L.lattice := fun n x hx => by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem n hx
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have h := L.lattice.neg_mem (D.mul _ D.ker)
    have e : -(sqrtNegNat p * (sqrtNegNat p * t)) = (p : ℂ) * t := by
      linear_combination (-t) * hsq
    rwa [e] at h
  have h1 : ∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k := by
    intro k
    constructor
    · intro hk
      by_contra hnd
      have hc : IsCoprime (p : ℤ) k := (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hnd
      obtain ⟨a, b, hab⟩ := hc
      apply D.notMem
      have h := L.lattice.add_mem (hz a _ hpt) (hz b _ hk)
      have hab' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast congrArg (Int.cast (R := ℂ)) hab
      have e : (a : ℂ) * ((p : ℂ) * t) + (b : ℂ) * ((k : ℂ) * t) = t := by
        linear_combination t * hab'
      rwa [e] at h
    · rintro ⟨c, rfl⟩
      have h := hz c _ hpt
      have e : (c : ℂ) * ((p : ℂ) * t) = (((p : ℤ) * c : ℤ) : ℂ) * t := by push_cast; ring
      rwa [e] at h
  have hker : ∀ k : ℕ, sqrtNegNat p * ((k : ℂ) * t) ∈ L.lattice := fun k => by
    have h := hz k _ D.ker
    have e : ((k : ℤ) : ℂ) * (sqrtNegNat p * t) = sqrtNegNat p * ((k : ℂ) * t) := by push_cast; ring
    rwa [e] at h
  have hnot : ∀ k ∈ Finset.Ico 1 p, (k : ℂ) * t ∉ L.lattice := fun k hk h => by
    rw [Finset.mem_Ico] at hk
    have h' : (p : ℤ) ∣ (k : ℤ) := (h1 k).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd hk.1 (Int.natCast_dvd_natCast.mp h')
    omega
  have hinj : ∀ k ∈ Finset.Ico 1 p, ∀ l ∈ Finset.Ico 1 p, (k : ℂ) * t - (l : ℂ) * t ∈ L.lattice → k = l := by
    intro k hk l hl h
    rw [Finset.mem_Ico] at hk hl
    have e : (k : ℂ) * t - (l : ℂ) * t = (((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * t := by push_cast; ring
    rw [e, h1] at h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    have h := congrArg Complex.normSq hsq
    rw [map_pow, Complex.normSq_neg, Complex.normSq_natCast, ← sq] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg _) hp0.le two_ne_zero).mp h
  have hα : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    exact hp0.ne hn
  obtain ⟨S, hS⟩ := kerRepsExist L _ hα D.mul
  have hcard : S.card + 1 = p := by
    have h := kerRepsCard L _ S hα D.mul hS
    rw [hn] at h
    exact_mod_cast h
  choose f hfS hf using fun k (hk : k ∈ Finset.Ico 1 p) => hS.2.2 _ (hker k) (hnot k hk)
  have hsurj := Finset.surj_on_of_inj_on_of_card_le f hfS
    (fun k l hk hl h => hinj k hk l hl (by
      have h' := L.lattice.sub_mem (hf k hk) (hf l hl)
      rw [h] at h'
      simpa using h'))
    (by rw [Nat.card_Ico]; omega)
  have h3 : ∀ z, sqrtNegNat p * z ∈ L.lattice → z ∉ L.lattice →
      ∃ k ∈ Finset.Ico 1 p, z - (k : ℂ) * t ∈ L.lattice := by
    intro z hz1 hz2
    obtain ⟨P, hP, hzP⟩ := hS.2.2 z hz1 hz2
    obtain ⟨k, hk, rfl⟩ := hsurj P hP
    refine ⟨k, hk, ?_⟩
    simpa using L.lattice.sub_mem hzP (hf k hk)
  refine ⟨h1, fun z hz1 => ?_, ?_, ?_, ?_⟩
  · by_cases hz2 : z ∈ L.lattice
    · exact ⟨0, hp.pos, by simpa using hz2⟩
    · obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
      exact ⟨k, (Finset.mem_Ico.mp hk).2, h⟩
  · intro P hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hker k, hnot k hk⟩
  · intro P hP Q hQ h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hQ
    rw [hinj k hk l hl h]
  · intro z hz1 hz2
    obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
    exact ⟨_, Finset.mem_image_of_mem _ hk, h⟩

end GlobalTheory.CMModel
