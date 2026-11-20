import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.FrobIterQModPrimeHolds
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.FiniteCocyclesLeCocycles
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.CocycleComponentRelation
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LemmaS
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.EulerCharacteristicHolds
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LowestComponent
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

noncomputable section

namespace Formalism.NOK

open PowerSeries

/- English proof (translation)
Simplify using `[Formalism.WachCohomologyFacts.Base.p]`. Rewrite using `[← Function.iterate_succ_apply, Function.iterate_succ_apply']`.
-/
theorem base_p_succ {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (B : Formalism.WachCohomologyFacts.Base O A) (s : ℕ) : B.p (s + 1) = B.φ (B.p s) := by
  simp [Formalism.WachCohomologyFacts.Base.p]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

/- English proof (translation)
Introduce `O A _ _ _ B j`. Establish `hp0 : B.p 0 = B.X + B.ℓ` using `by simp [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨1, isUnit_one, by simp⟩`. Consider the case `succ j ih`.

Take `⟨v, hv, hj⟩` from `ih`. Use `⟨B.φ v * B.u, (hv.map B.φ).mul B.8, ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', hj, map_mul, map_mul, map_prod, B.12, Finset.prod_range_succ']`. Simplify using `only [map_pow, ← base_p_succ]`. Rewrite using `[hp0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiIterX_proof : PhiIterX := by
  intro O A _ _ _ B j
  have hp0 : B.p 0 = B.X + B.ℓ := by simp [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]
  induction j with
  | zero => exact ⟨1, isUnit_one, by simp⟩
  | succ j ih =>
    obtain ⟨v, hv, hj⟩ := ih
    refine ⟨B.φ v * B.u, (hv.map B.φ).mul B.8, ?_⟩
    rw [Function.iterate_succ_apply', hj, map_mul, map_mul, map_prod, B.12, Finset.prod_range_succ']
    simp only [map_pow, ← base_p_succ]
    rw [hp0]
    ring

/- English proof (translation)
Introduce `O A _ _ _ B s`. Establish `hX : ∀ s, (⇑B.φ)^[s] B.X ∈ Ideal.span {(B.ℓ : A), B.X ^ B.ℓ ^ s}`. Introduce `s`. Proceed by induction on `s with`. Consider the case `zero => exact Ideal.subset_span (by simp)`.

Consider the case `succ s ih`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.mp ih`. Establish `hℓ1 : B.ℓ - 1 + 1 = B.ℓ` using `Nat.sub_add_cancel B.2.one_lt.le`. Establish `hXpow : B.X ^ B.ℓ = B.X ^ (B.ℓ - 1) * B.X` using `by rw [← pow_succ, hℓ1]`. Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow (B.X + (B.ℓ : A)) B.X (B.ℓ - 1)`.

Establish `e3 : B.φ B.X = B.u * B.X ^ B.ℓ + B.u * B.X * c * (B.ℓ : A)`. Rewrite using `[B.12, hXpow]`. Take the linear combination `(B.u * B.X) * hc`. Take `⟨e, he⟩` from `sub_dvd_pow_sub_pow (B.φ B.X) (B.u * B.X ^ B.ℓ) (B.ℓ ^ s)`. Establish `e1 : (⇑B.φ)^[s + 1] B.X = B.φ a * B.ℓ + B.φ b * (B.φ B.X) ^ B.ℓ ^ s`.

Rewrite using `[Function.iterate_succ_apply', ← hab, map_add, map_mul, map_mul, map_pow, map_natCast]`. Establish `e4 : B.X ^ B.ℓ ^ (s + 1) = (B.X ^ B.ℓ) ^ B.ℓ ^ s` using `by rw [← pow_mul, pow_succ']`. Use `Ideal.mem_span_pair.mpr ⟨B.φ a + B.φ b * (B.u * B.X * c) * e, B.φ b * B.u ^ B.ℓ ^ s, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, e4]`. Take the linear combination `(-(B.φ b)) * he - (B.φ b * e) * e3`.

Establish `hadd : ∀ s, (⇑B.φ)^[s] (B.X + (B.ℓ : A)) = (⇑B.φ)^[s] B.X + B.ℓ`. Introduce `s`. Proceed by induction on `s with`. Consider the case `zero => rfl`. Consider the case `succ s ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add, map_natCast]`.

Simplify using `only [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]`. Rewrite using `[hadd]`. Conclude with `Ideal.add_mem _ (hX s) (Ideal.subset_span (by simp))`.
-/
theorem psIdeal_proof : PsIdeal := by
  intro O A _ _ _ B s
  have hX : ∀ s, (⇑B.φ)^[s] B.X ∈ Ideal.span {(B.ℓ : A), B.X ^ B.ℓ ^ s} := by
    intro s
    induction s with
    | zero => exact Ideal.subset_span (by simp)
    | succ s ih =>
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp ih
      have hℓ1 : B.ℓ - 1 + 1 = B.ℓ := Nat.sub_add_cancel B.2.one_lt.le
      have hXpow : B.X ^ B.ℓ = B.X ^ (B.ℓ - 1) * B.X := by rw [← pow_succ, hℓ1]
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (B.X + (B.ℓ : A)) B.X (B.ℓ - 1)
      have e3 : B.φ B.X = B.u * B.X ^ B.ℓ + B.u * B.X * c * (B.ℓ : A) := by
        rw [B.12, hXpow]
        linear_combination (B.u * B.X) * hc
      obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (B.φ B.X) (B.u * B.X ^ B.ℓ) (B.ℓ ^ s)
      have e1 : (⇑B.φ)^[s + 1] B.X = B.φ a * B.ℓ + B.φ b * (B.φ B.X) ^ B.ℓ ^ s := by
        rw [Function.iterate_succ_apply', ← hab, map_add, map_mul, map_mul, map_pow, map_natCast]
      have e4 : B.X ^ B.ℓ ^ (s + 1) = (B.X ^ B.ℓ) ^ B.ℓ ^ s := by rw [← pow_mul, pow_succ']
      refine Ideal.mem_span_pair.mpr ⟨B.φ a + B.φ b * (B.u * B.X * c) * e, B.φ b * B.u ^ B.ℓ ^ s, ?_⟩
      rw [e1, e4]
      linear_combination (-(B.φ b)) * he - (B.φ b * e) * e3
  have hadd : ∀ s, (⇑B.φ)^[s] (B.X + (B.ℓ : A)) = (⇑B.φ)^[s] B.X + B.ℓ := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add, map_natCast]
  simp only [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]
  rw [hadd]
  exact Ideal.add_mem _ (hX s) (Ideal.subset_span (by simp))

/- English proof (translation)
Introduce `ℓ _ hℓ2 χ hχ r`. Establish `hp : ℓ.Prime` using `Fact.out`. Establish `hℓ1 : 1 ≤ ℓ - 1` using `by have := hp.two_le; omega`. Establish `hz` using `Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ2) (by exact_mod_cast hχ) ((ℓ - 1 : ℕ) : ℤ) (by exact_mod_cast (show ℓ - 1 ≠ 0 by omega))`. Establish `hnd : ¬ ℓ ∣ ℓ - 1` using `Nat.not_dvd_of_pos_of_lt (by omega) (by omega)`.

Rewrite `hz` using `[zpow_natCast, padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd hnd]`. Establish `hvp` using `(Formalism.WindowSums.arc_ValProd ℓ (χ ^ (ℓ - 1)) 1 le_rfl (fun h => absurd h hℓ2) (by rw [hz.2])).1 r`. Establish `heq : ∀ y, ((χ ^ (ℓ - 1) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ^ y = (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * y)`. Introduce `y`. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul]`.

Simplify using `only [heq, mul_one] at hvp`. Conclude with `hvp`.
-/
theorem delVal_proof : DelVal := by
  intro ℓ _ hℓ2 χ hχ r
  have hp : ℓ.Prime := Fact.out
  have hℓ1 : 1 ≤ ℓ - 1 := by have := hp.two_le; omega
  have hz := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ2) (by exact_mod_cast hχ)
    ((ℓ - 1 : ℕ) : ℤ) (by exact_mod_cast (show ℓ - 1 ≠ 0 by omega))
  have hnd : ¬ ℓ ∣ ℓ - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd hnd] at hz
  have hvp := (Formalism.WindowSums.arc_ValProd ℓ (χ ^ (ℓ - 1)) 1 le_rfl (fun h => absurd h hℓ2)
    (by rw [hz.2])).1 r
  have heq : ∀ y, ((χ ^ (ℓ - 1) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ^ y = (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * y) := by
    intro y; rw [Units.val_pow_eq_pow_val, pow_mul]
  simp only [heq, mul_one] at hvp
  exact hvp

/- English proof (translation)
Introduce `O _ _ ϖ hϖ p v N hN hv h c hc`. Rewrite `h` using `[Ideal.mem_span_singleton]`. Take `⟨q, hq⟩` from `h`. Rewrite `hc` using `[Ideal.mem_span_pair]`. Take `⟨a, b, hab⟩` from `hc`.

Establish `hp0 : PowerSeries.constantCoeff p = ϖ * PowerSeries.constantCoeff q`. Establish `h1` using `congrArg PowerSeries.constantCoeff hq`. Simplify using `only [map_sub, map_mul, PowerSeries.constantCoeff_C, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : N ≠ 0), mul_zero, sub_zero] at h1`. Conclude with `h1`. Establish `hc0` using `congrArg PowerSeries.constantCoeff hab`.

Simplify using `only [map_add, map_mul, PowerSeries.constantCoeff_C, hp0] at hc0`. Conclude with `⟨PowerSeries.constantCoeff a + PowerSeries.constantCoeff b * PowerSeries.constantCoeff q, by`. Rewrite using `[← hc0]`. Use the proof step `ring⟩`.
-/
theorem dSat_proof : DSat := by
  intro O _ _ ϖ hϖ p v N hN hv h c hc
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  rw [Ideal.mem_span_pair] at hc
  obtain ⟨a, b, hab⟩ := hc
  have hp0 : PowerSeries.constantCoeff p = ϖ * PowerSeries.constantCoeff q := by
    have h1 := congrArg PowerSeries.constantCoeff hq
    simp only [map_sub, map_mul, PowerSeries.constantCoeff_C, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (by omega : N ≠ 0), mul_zero, sub_zero] at h1
    exact h1
  have hc0 := congrArg PowerSeries.constantCoeff hab
  simp only [map_add, map_mul, PowerSeries.constantCoeff_C, hp0] at hc0
  exact ⟨PowerSeries.constantCoeff a + PowerSeries.constantCoeff b * PowerSeries.constantCoeff q, by
    rw [← hc0]
    ring⟩

/- English proof (translation)
Introduce `O _ _ ϖ hϖ ℓ p₀ p₁ v₀ v₁ w s₀ s₁ b₀ b₁ hs hb hv₀ hv₁ hw h₀ h₁ hmem`. Use `haveI hpr : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ`. Establish `hϖ0 : (Ideal.Quotient.mk (Ideal.span {ϖ})) ϖ = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)`. Establish `hred : ∀ (p v : PowerSeries O) (N : ℕ), p - v * X ^ N ∈ Ideal.span {C ϖ} → PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p = PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v * X ^ N`. Introduce `p v N h`.

Rewrite `h` using `[Ideal.mem_span_singleton]`. Take `⟨q, hq⟩` from `h`. Establish `h0` using `congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hq`. Simplify using `only [map_mul, map_sub, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero, zero_mul] at h0`. Conclude with `sub_eq_zero.mp h0`.

Establish `hℓ : 1 ≤ ℓ` using `Nat.pos_of_ne_zero (fun h => by simp [h] at hb)`. Establish `h1 : ℓ ^ s₀ * ℓ ≤ ℓ ^ s₁`. Rewrite using `[← pow_succ]`. Conclude with `Nat.pow_le_pow_right hℓ hs`. Establish `h2 : 0 < ℓ ^ s₀` using `pow_pos hℓ _`.

Establish `hlt : ℓ ^ s₀ * b₀ < ℓ ^ s₁ * b₁` using `by nlinarith`. Rewrite `hmem` using `[Ideal.mem_span_pair]`. Take `⟨a, b, hab⟩` from `hmem`. Establish `hm` using `congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hab`. Simplify using `only [map_add, map_mul, map_pow, PowerSeries.map_C, hϖ0, map_zero, mul_zero, zero_add] at hm`.

Rewrite `hm` using `[hred p₀ v₀ _ h₀, hred p₁ v₁ _ h₁, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc]`. Establish `hc` using `congrArg (PowerSeries.coeff (ℓ ^ s₀ * b₀)) hm`. Rewrite `hc` using `[PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hlt), if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Establish `hu : IsUnit (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v₀ ^ b₀)` using `(hw.map _).mul ((hv₀.map _).pow _)`. Conclude with `(hu.map PowerSeries.constantCoeff).ne_zero hc.symm`.
-/
theorem dUDeg_proof : DUDeg := by
  intro O _ _ ϖ hϖ ℓ p₀ p₁ v₀ v₁ w s₀ s₁ b₀ b₁ hs hb hv₀ hv₁ hw h₀ h₁ hmem
  haveI hpr : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  have hϖ0 : (Ideal.Quotient.mk (Ideal.span {ϖ})) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have hred : ∀ (p v : PowerSeries O) (N : ℕ), p - v * X ^ N ∈ Ideal.span {C ϖ} →
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p = PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v * X ^ N := by
    intro p v N h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨q, hq⟩ := h
    have h0 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hq
    simp only [map_mul, map_sub, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero, zero_mul] at h0
    exact sub_eq_zero.mp h0
  have hℓ : 1 ≤ ℓ := Nat.pos_of_ne_zero (fun h => by simp [h] at hb)
  have h1 : ℓ ^ s₀ * ℓ ≤ ℓ ^ s₁ := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right hℓ hs
  have h2 : 0 < ℓ ^ s₀ := pow_pos hℓ _
  have hlt : ℓ ^ s₀ * b₀ < ℓ ^ s₁ * b₁ := by nlinarith
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hm := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hab
  simp only [map_add, map_mul, map_pow, PowerSeries.map_C, hϖ0, map_zero, mul_zero, zero_add] at hm
  rw [hred p₀ v₀ _ h₀, hred p₁ v₁ _ h₁, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc] at hm
  have hc := congrArg (PowerSeries.coeff (ℓ ^ s₀ * b₀)) hm
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hlt), if_pos le_rfl,
    Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
  have hu : IsUnit (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v₀ ^ b₀) :=
    (hw.map _).mul ((hv₀.map _).pow _)
  exact (hu.map PowerSeries.constantCoeff).ne_zero hc.symm

end Formalism.NOK
