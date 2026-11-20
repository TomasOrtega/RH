import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPB

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo.ChainBetweenPairs

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.F (scalePair MulStable)

/- English proof (translation)
Establish `hω2` using `omega_sq d (by omega)`. Use `set πb : ℂ := ((X + Y : ℤ) : ℂ) + ((-Y : ℤ) : ℂ) * omegaK d with hπb`. Establish `hNc : (X : ℂ) ^ 2 + X * Y + (((d + 1) / 4 : ℕ) : ℂ) * Y ^ 2 = 2 ^ h`. Use `congrArg (Int.cast : ℤ → ℂ) hN` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hprod : π * πb = 2 ^ h`. Rewrite using `[hπ, hπb]`. Use `push_cast`. Take the linear combination `(-(Y : ℂ) ^ 2) * hω2 + hNc`.

Establish `hπ0 : π ≠ 0`. Introduce `h0`. Rewrite `hprod` using `[h0, zero_mul]`. Conclude with `(pow_ne_zero h two_ne_zero) hprod.symm`. Establish `stπ : ∀ z ∈ L.lattice, π * z ∈ L.lattice` using `fun z hz => hπ ▸ stab d L hL X Y hz`.

Establish `stπb : ∀ z ∈ L.lattice, πb * z ∈ L.lattice` using `fun z hz => stab d L hL (X + Y) (-Y) hz`. Establish `hle1 : ∀ i, L.lattice ≤ S L π i` using `fun i z hz => ⟨stπ z hz, pow_two_mul_mem L i hz⟩`. Establish `hle2 : ∀ i, S L π i ≤ (scalePair L π⁻¹ (inv_ne_zero hπ0)).lattice`. Introduce `i z hz`. Rewrite using `[(Formalism.L2.Th1.F.homogeneity L π⁻¹ (inv_ne_zero hπ0)).1 z, inv_inv]`.

Conclude with `hz.1`. Use `choose P hP using fun i => exists_pair_of_between L _ (S L π i) (hle1 i) (hle2 i)`. Set `M : ℕ → PeriodPair` to `fun i => if i = 0 then L else P i`. Establish `hM : ∀ i z, z ∈ (M i).lattice ↔ z ∈ S L π i`. Introduce `i z`.

Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Simplify using `only [M, if_pos rfl, mem_S, pow_zero, one_mul]`. Conclude with `⟨fun hz => ⟨stπ z hz, hz⟩, fun hz => hz.2⟩`. Simplify using `only [M, if_neg hi]`.

Conclude with `hP i z`. Establish `claimA : ∀ i u v, u ∈ S L π (i + 1) → v ∈ S L π (i + 1) → u ∉ S L π i → v ∉ S L π i → u - v ∈ S L π i`. Introduce `i u v hu hv hu3 hv3`. Establish `hnh : ¬ MulStable L (π / 2)`. Rewrite using `[hπ]`.

Conclude with `not_half d L X Y hY`. Establish `key` using `two_tors L π hnh stπ (u := (2 : ℂ) ^ i * u) (v := (2 : ℂ) ^ i * v) (by rw [mul_left_comm]; exact pow_two_mul_mem L i hu.1) (by rw [← mul_assoc, ← pow_succ']; exact hu.2) (fun h' => hu3 ⟨hu.1, h'⟩) (by rw [mul_left_comm]; exact pow_two_mul_mem L i hv.1) (by rw [← mul_assoc, ← pow_ …`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sub]`. Conclude with `sub_mem hu.1 hv.1`.

Rewrite using `[mul_sub]`. Conclude with `key`. Use `⟨M, by simp [M], ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i z hz`. Rewrite `hz`, the goal using `[hM]`.

Conclude with `⟨by rw [mul_left_comm]; exact hL _ hz.1, by rw [mul_left_comm]; exact hL _ hz.2⟩`. Introduce `i hi`. Establish `hns : ¬ MulStable L (πb / 2)` using `not_half d L (X + Y) (-Y) hY.neg`. Unfold `MulStable at hns`. Use `push Not at hns`.

Take `⟨w, hw, hw2⟩` from `hns`. Take `⟨j, rfl⟩ : ∃ j, h = i + j + 1` from `⟨h - i - 1, by omega⟩`. Establish `hπb' : πb = 2 ^ (i + j + 1) / π` using `(eq_div_iff hπ0).2 (by rw [mul_comm]; exact hprod)`. Use `set t : ℂ := (2 : ℂ) ^ j * (w / π) with ht`. Establish `htπ : π * t = (2 : ℂ) ^ j * w`.

Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts. Establish `ht2 : (2 : ℂ) ^ i * t = πb / 2 * w`. Rewrite using `[ht, hπb']`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `ht3 : (2 : ℂ) ^ (i + 1) * t = πb * w`. Rewrite using `[pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc, ht2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmono : ∀ z, z ∈ S L π i → z ∈ S L π (i + 1)`.

Introduce `z hz`. Use `⟨hz.1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc]`. Use `pow_two_mul_mem L 1 hz.2` as an intermediate fact. Simplify using `using this`.

Establish `htS1 : t ∈ S L π (i + 1)` using `⟨by rw [htπ]; exact pow_two_mul_mem L j hw, by rw [ht3]; exact stπb _ hw⟩`. Establish `htS0 : t ∉ S L π i` using `fun h' => hw2 (by rw [← ht2]; exact h'.2)`. Use `⟨t, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hM]`. Conclude with `htS0`.

Rewrite using `[hM]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, htπ]`. Use `pow_two_mul_mem L 1 (pow_two_mul_mem L j hw)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[mul_left_comm, ht2]`. Establish `: 2 * (πb / 2 * w) = πb * w` using `by ring`. Rewrite using `[this]`. Conclude with `stπb _ hw`. Introduce `z`.

Rewrite using `[hM, hM, hM]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Distinguish the cases in `hz' : z ∈ S L π i`. Conclude with `Or.inl hz'`.

Conclude with `Or.inr (claimA i z t hz htS1 hz' htS0)`. Introduce and unpack `(hz | hz)`. Conclude with `hmono z hz`. Establish `: z = (z - t) + t` using `by ring`. Rewrite using `[this]`.

Conclude with `add_mem (hmono _ hz) htS1`. Introduce `z`. Rewrite using `[hM, mem_S]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hz => hz.1`.

Introduce `hz`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Establish `: (2 : ℂ) ^ h * z = πb * (π * z)` using `by rw [← hprod]; ring`. Rewrite using `[this]`. Conclude with `stπb _ hz`.
-/
theorem chain_core (d : ℕ) (L : PeriodPair) (hd : d % 8 = 7) (hL : HasCMBy d L) (h : ℕ) (X Y : ℤ)
    (hY : Odd Y) (hN : X ^ 2 + X * Y + (((d + 1) / 4 : ℕ) : ℤ) * Y ^ 2 = 2 ^ h) (π : ℂ)
    (hπ : π = X + Y * omegaK d) :
    ∃ M : ℕ → PeriodPair, M 0 = L ∧ (∀ i, HasCMBy d (M i)) ∧
      (∀ i, i < h → IsIdxTwo (M i) (M (i + 1))) ∧ ∀ z, z ∈ (M h).lattice ↔ π * z ∈ L.lattice := by
  have hω2 := omega_sq d (by omega)
  set πb : ℂ := ((X + Y : ℤ) : ℂ) + ((-Y : ℤ) : ℂ) * omegaK d with hπb
  have hNc : (X : ℂ) ^ 2 + X * Y + (((d + 1) / 4 : ℕ) : ℂ) * Y ^ 2 = 2 ^ h := by
    have := congrArg (Int.cast : ℤ → ℂ) hN
    push_cast at this
    exact this
  have hprod : π * πb = 2 ^ h := by
    rw [hπ, hπb]
    push_cast
    linear_combination (-(Y : ℂ) ^ 2) * hω2 + hNc
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact (pow_ne_zero h two_ne_zero) hprod.symm
  have stπ : ∀ z ∈ L.lattice, π * z ∈ L.lattice := fun z hz => hπ ▸ stab d L hL X Y hz
  have stπb : ∀ z ∈ L.lattice, πb * z ∈ L.lattice := fun z hz => stab d L hL (X + Y) (-Y) hz
  have hle1 : ∀ i, L.lattice ≤ S L π i := fun i z hz => ⟨stπ z hz, pow_two_mul_mem L i hz⟩
  have hle2 : ∀ i, S L π i ≤ (scalePair L π⁻¹ (inv_ne_zero hπ0)).lattice := by
    intro i z hz
    rw [(Formalism.L2.Th1.F.homogeneity L π⁻¹ (inv_ne_zero hπ0)).1 z, inv_inv]
    exact hz.1
  choose P hP using fun i => exists_pair_of_between L _ (S L π i) (hle1 i) (hle2 i)
  let M : ℕ → PeriodPair := fun i => if i = 0 then L else P i
  have hM : ∀ i z, z ∈ (M i).lattice ↔ z ∈ S L π i := by
    intro i z
    by_cases hi : i = 0
    · subst hi
      simp only [M, if_pos rfl, mem_S, pow_zero, one_mul]
      exact ⟨fun hz => ⟨stπ z hz, hz⟩, fun hz => hz.2⟩
    · simp only [M, if_neg hi]
      exact hP i z

  have claimA : ∀ i u v, u ∈ S L π (i + 1) → v ∈ S L π (i + 1) → u ∉ S L π i → v ∉ S L π i →
      u - v ∈ S L π i := by
    intro i u v hu hv hu3 hv3
    have hnh : ¬ MulStable L (π / 2) := by
      rw [hπ]
      exact not_half d L X Y hY
    have key := two_tors L π hnh stπ (u := (2 : ℂ) ^ i * u) (v := (2 : ℂ) ^ i * v)
      (by rw [mul_left_comm]; exact pow_two_mul_mem L i hu.1)
      (by rw [← mul_assoc, ← pow_succ']; exact hu.2) (fun h' => hu3 ⟨hu.1, h'⟩)
      (by rw [mul_left_comm]; exact pow_two_mul_mem L i hv.1)
      (by rw [← mul_assoc, ← pow_succ']; exact hv.2) (fun h' => hv3 ⟨hv.1, h'⟩)
    refine ⟨?_, ?_⟩
    · rw [mul_sub]
      exact sub_mem hu.1 hv.1
    · rw [mul_sub]
      exact key
  refine ⟨M, by simp [M], ?_, ?_, ?_⟩
  · intro i z hz
    rw [hM] at hz ⊢
    exact ⟨by rw [mul_left_comm]; exact hL _ hz.1, by rw [mul_left_comm]; exact hL _ hz.2⟩
  · intro i hi
    have hns : ¬ MulStable L (πb / 2) := not_half d L (X + Y) (-Y) hY.neg
    unfold MulStable at hns
    push Not at hns
    obtain ⟨w, hw, hw2⟩ := hns
    obtain ⟨j, rfl⟩ : ∃ j, h = i + j + 1 := ⟨h - i - 1, by omega⟩
    have hπb' : πb = 2 ^ (i + j + 1) / π := (eq_div_iff hπ0).2 (by rw [mul_comm]; exact hprod)
    set t : ℂ := (2 : ℂ) ^ j * (w / π) with ht
    have htπ : π * t = (2 : ℂ) ^ j * w := by
      rw [ht]
      field_simp
    have ht2 : (2 : ℂ) ^ i * t = πb / 2 * w := by
      rw [ht, hπb']
      field_simp
      ring
    have ht3 : (2 : ℂ) ^ (i + 1) * t = πb * w := by
      rw [pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc, ht2]
      ring
    have hmono : ∀ z, z ∈ S L π i → z ∈ S L π (i + 1) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc]
      have := pow_two_mul_mem L 1 hz.2
      simpa using this
    have htS1 : t ∈ S L π (i + 1) := ⟨by rw [htπ]; exact pow_two_mul_mem L j hw, by rw [ht3]; exact stπb _ hw⟩
    have htS0 : t ∉ S L π i := fun h' => hw2 (by rw [← ht2]; exact h'.2)
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [hM]
      exact htS0
    · rw [hM]
      refine ⟨?_, ?_⟩
      · rw [mul_left_comm, htπ]
        have := pow_two_mul_mem L 1 (pow_two_mul_mem L j hw)
        simpa using this
      · rw [mul_left_comm, ht2]
        have : 2 * (πb / 2 * w) = πb * w := by ring
        rw [this]
        exact stπb _ hw
    · intro z
      rw [hM, hM, hM]
      constructor
      · intro hz
        by_cases hz' : z ∈ S L π i
        · exact Or.inl hz'
        · exact Or.inr (claimA i z t hz htS1 hz' htS0)
      · rintro (hz | hz)
        · exact hmono z hz
        · have : z = (z - t) + t := by ring
          rw [this]
          exact add_mem (hmono _ hz) htS1
  · intro z
    rw [hM, mem_S]
    constructor
    · exact fun hz => hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      have : (2 : ℂ) ^ h * z = πb * (π * z) := by rw [← hprod]; ring
      rw [this]
      exact stπb _ hz

end PI.GoodTwo.ChainBetweenPairs
