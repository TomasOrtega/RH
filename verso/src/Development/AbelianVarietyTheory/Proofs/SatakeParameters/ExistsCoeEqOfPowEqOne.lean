import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.MainNotions.GL3Theta IsLocalRing Polynomial

/- English proof (translation)
Establish `hs : (X ^ n - C 1 : (PadicAlgCl l)[X]).Splits` using `IsAlgClosed.splits _`. Establish `hne : (X ^ n - C 1 : (PadicAlgCl l)[X]) ≠ 0` using `X_pow_sub_C_ne_zero hn 1`. Establish `hr : ((X ^ n - C 1 : (PadicAlgCl l)[X]).map (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot ζ`. Simplify using `[h]`. Take `⟨a, ha⟩` from `hs.mem_range_of_isRoot hne hr`.

Use `⟨a, ha, (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, ha, h, map_one]`.
-/
theorem exists_coe_eq_of_pow_eq_one (l : ℕ) [Fact l.Prime] (ζ : ℂ_[l]) (n : ℕ) (hn : 0 < n)
    (h : ζ ^ n = 1) : ∃ a : PadicAlgCl l, (a : ℂ_[l]) = ζ ∧ a ^ n = 1 := by
  have hs : (X ^ n - C 1 : (PadicAlgCl l)[X]).Splits := IsAlgClosed.splits _
  have hne : (X ^ n - C 1 : (PadicAlgCl l)[X]) ≠ 0 := X_pow_sub_C_ne_zero hn 1
  have hr : ((X ^ n - C 1 : (PadicAlgCl l)[X]).map (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot ζ := by
    simp [h]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot hne hr
  refine ⟨a, ha, (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  rw [map_pow, ha, h, map_one]

/- English proof (translation)
Establish `e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l` using `PadicInt.residueField`. Establish `hl : l.Prime` using `Fact.out`. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Establish `hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l`. Rewrite using `[Nat.card_congr e.toEquiv, Nat.card_zmod]`.

Take `⟨φ, hφ⟩` from `GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)`. Rewrite `hφ` using `[hcard]`. Use `⟨φ, fun x m hm hx => hφ x m (fun h => ?_) hx⟩` and prove the remaining obligations. Rewrite `h` using `[← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff]`. Conclude with `(hl.coprime_iff_not_dvd.1 hm.symm) h`.
-/
theorem exists_gal_pow (l : ℕ) [Fact l.Prime] :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l,
      ∀ (x : PadicAlgCl l) (m : ℕ), Nat.Coprime m l → x ^ m = 1 → g x = x ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  rw [hcard] at hφ
  refine ⟨φ, fun x m hm hx => hφ x m (fun h => ?_) hx⟩
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
  exact (hl.coprime_iff_not_dvd.1 hm.symm) h

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hl0 : (l : ℂ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hl.ne_zero`. Establish `hc : Continuous σ` using `(AddMonoidHomClass.isometry_of_norm σ hσ).continuous`. Use `⟨hσ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (Wp l : Set ℂ_[l])` using `Subring.isClosed_topologicalClosure _`.

Establish `hA : ∀ x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1}, ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y`. Introduce `x hx`. Establish `hW : ∀ {x}, x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} → x ∈ Wp l` using `fun h => Subring.le_topologicalClosure _ h`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`.

Take `⟨n, hn, hnl, h⟩` from `hx`. Conclude with `⟨0, zero_mem _, by simp [hζ x n hn hnl h]⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp [hl.ne_zero]⟩`. Consider the case `one => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y hx hy ihx ihy`.

Take `⟨a, ha, ea⟩` from `ihx`. Take `⟨b, hb, eb⟩` from `ihy`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hl (⟨x, hW hx⟩ : Wp l) ⟨y, hW hy⟩`. Establish `hr'` using `congrArg Subtype.val hr`. Move the coercions through the operations in `at hr'`.

Use `⟨a + b - x * y * r, sub_mem (add_mem ha hb) (mul_mem (mul_mem (hW hx) (hW hy)) r.2), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ea, eb, hr']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x hx ihx`. Take `⟨a, ha, ea⟩` from `ihx`.

Break down `hl.eq_two_or_odd' with h2 | ho` into its components or cases. Use `⟨-a - x ^ l, sub_mem (neg_mem ha) (pow_mem (hW hx) _), ?_⟩` and prove the remaining obligations. Establish `he : Even l` using `h2 ▸ even_two`. Establish `h2' : (l : ℂ_[l]) = 2` using `by exact_mod_cast h2`. Rewrite using `[map_neg, ea, he.neg_pow]`.

Take the linear combination `(x ^ l) * h2'`. Use `⟨-a, neg_mem ha, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ea, ho.neg_pow]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y hx hy ihx ihy`.

Take `⟨a, ha, ea⟩` from `ihx`. Take `⟨b, hb, eb⟩` from `ihy`. Use `⟨a * y ^ l + x ^ l * b + l * (a * b), add_mem (add_mem (mul_mem ha (pow_mem (hW hy) _)) (mul_mem (pow_mem (hW hx) _) hb)) (mul_mem (natCast_mem _ _) (mul_mem ha hb)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ea, eb, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hf : Continuous fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹` using `by fun_prop`. Establish `hx' : x ∈ (fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹) ⁻¹' (Wp l : Set ℂ_[l])`. Use `closure_minimal (fun z hz => ?_) (hcl.preimage hf) hx` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hA z hz`. Establish `: (σ z - z ^ l) * (l : ℂ_[l])⁻¹ = y`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify `hy` using `[this]`. Use `⟨_, hx', ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isFrob_of_rootOfUnity {l : ℕ} [Fact l.Prime] (σ : ℂ_[l] →+* ℂ_[l]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[l]) (n : ℕ), 0 < n → Nat.Coprime n l → ζ ^ n = 1 → σ ζ = ζ ^ l) : IsFrob σ := by
  have hl : l.Prime := Fact.out
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine ⟨hσ, fun x hx => ?_⟩
  have hcl : IsClosed (Wp l : Set ℂ_[l]) := Subring.isClosed_topologicalClosure _
  have hA : ∀ x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1},
      ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y := by
    intro x hx
    have hW : ∀ {x}, x ∈ Subring.closure
        {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} → x ∈ Wp l :=
      fun h => Subring.le_topologicalClosure _ h
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn, hnl, h⟩ := hx
      exact ⟨0, zero_mem _, by simp [hζ x n hn hnl h]⟩
    | zero => exact ⟨0, zero_mem _, by simp [hl.ne_zero]⟩
    | one => exact ⟨0, zero_mem _, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (⟨x, hW hx⟩ : Wp l) ⟨y, hW hy⟩
      have hr' := congrArg Subtype.val hr
      push_cast at hr'
      refine ⟨a + b - x * y * r, sub_mem (add_mem ha hb)
        (mul_mem (mul_mem (hW hx) (hW hy)) r.2), ?_⟩
      rw [map_add, ea, eb, hr']
      ring
    | neg x hx ihx =>
      obtain ⟨a, ha, ea⟩ := ihx
      rcases hl.eq_two_or_odd' with h2 | ho
      · refine ⟨-a - x ^ l, sub_mem (neg_mem ha) (pow_mem (hW hx) _), ?_⟩
        have he : Even l := h2 ▸ even_two
        have h2' : (l : ℂ_[l]) = 2 := by exact_mod_cast h2
        rw [map_neg, ea, he.neg_pow]
        linear_combination (x ^ l) * h2'
      · refine ⟨-a, neg_mem ha, ?_⟩
        rw [map_neg, ea, ho.neg_pow]
        ring
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      refine ⟨a * y ^ l + x ^ l * b + l * (a * b), add_mem (add_mem (mul_mem ha (pow_mem (hW hy) _))
        (mul_mem (pow_mem (hW hx) _) hb)) (mul_mem (natCast_mem _ _) (mul_mem ha hb)), ?_⟩
      rw [map_mul, ea, eb, mul_pow]
      ring
  have hf : Continuous fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹ := by fun_prop
  have hx' : x ∈ (fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹) ⁻¹' (Wp l : Set ℂ_[l]) := by
    refine closure_minimal (fun z hz => ?_) (hcl.preimage hf) hx
    obtain ⟨y, hy, e⟩ := hA z hz
    have : (σ z - z ^ l) * (l : ℂ_[l])⁻¹ = y := by
      rw [e]; field_simp; ring
    simpa [this] using hy
  refine ⟨_, hx', ?_⟩
  field_simp
  ring

end GlobalTheory.ThBe0
