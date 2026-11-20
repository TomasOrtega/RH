import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

/- English proof (translation)
Proceed by induction on `rs with`. Consider the case `nil`. Introduce `M _ _ _ y hy _ _`. Establish `hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤`. Introduce `h`.

Establish `h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y}` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[Submodule.mem_colon_singleton, one_smul]`. Conclude with `hy ((Submodule.mem_bot R).mp h1)`. Use `Ideal.Quotient.nontrivial_iff.mpr hne` as an intermediate fact. Simplify using `using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))`.

Consider the case `cons x rs ih`. Introduce `M _ _ _ y hy hmem hreg`. Establish `hx : x ∈ maximalIdeal R` using `hmem x List.mem_cons_self`. Establish `hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R` using `fun r hr => hmem r (List.mem_cons_of_mem x hr)`. Take `⟨hxreg, hrs⟩` from `(isWeaklyRegular_cons_iff M x rs).mp hreg`.

Establish `hspan : Ideal.span {x} ≠ ⊤` using `fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan`. Establish `hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤` using `fun k => by`. Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]`. Establish `hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M)` using `by by_contra! h`.

Conclude with `hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))`. Set `n` to `Nat.find hex`. Establish `hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M)` using `Nat.find_spec hex`. Establish `hn0 : n ≠ 0`. Introduce `h0`.

Apply `hn` to reduce the goal to its premises. Rewrite using `[h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]`. Conclude with `Submodule.mem_top`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hn0`. Establish `hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M)`.

Use `Nat.find_min hex (show k < n by omega)` as an intermediate fact. Simplify using `using this`. Rewrite `hyk`, `hn` using `[hpow]`. Take `⟨y₁, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk`. Establish `hy₁ : y₁ ∉ (x • ⊤ : Submodule R M)`.

Introduce `h`. Take `⟨z, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h`. Apply `hn` to reduce the goal to its premises. Rewrite using `[hk, smul_smul, ← pow_succ]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top`.

Establish `hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} = Submodule.colon (⊥ : Submodule R M) {y₁}`. Use extensionality with `r`. Simplify using `only [Submodule.mem_colon_singleton, Submodule.mem_bot]`. Rewrite using `[smul_comm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])`. Introduce `h`. Rewrite using `[h, smul_zero]`. Rewrite using `[hcolon]`.

Use `set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI`. Use `set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar`. Establish `hybar0 : ybar ≠ 0`. Rewrite using `[hybar, Ne, Submodule.Quotient.mk_eq_zero]`. Conclude with `hy₁`.

Establish `hih` using `ih ybar hybar0 hmem' hrs`. Establish `hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `r hr`. Rewrite `hr` using `[hI, Submodule.mem_colon_singleton, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr, Submodule.Quotient.mk_zero]`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top`. Establish `hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x}))` using `ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)`. Establish `hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I)`.

Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `z hz`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite `hz` using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot, mul_smul, smul_comm]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]`.

Conclude with `hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])`. Establish `hd2` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd`. Establish `heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x})`. Establish `: Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Rewrite using `[this]`. Conclude with `DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})`. Rewrite `hd2` using `[ringKrullDim_eq_of_ringEquiv heq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem length_le_ringKrullDim_quotient_colon {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by
  induction rs with
  | nil =>
    intro M _ _ _ y hy _ _
    have hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤ := by
      intro h
      have h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y} := h ▸ Submodule.mem_top
      rw [Submodule.mem_colon_singleton, one_smul] at h1
      exact hy ((Submodule.mem_bot R).mp h1)
    have := Ideal.Quotient.nontrivial_iff.mpr hne
    simpa using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))
  | cons x rs ih =>
    intro M _ _ _ y hy hmem hreg
    have hx : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hxreg, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg

    have hspan : Ideal.span {x} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan
    have hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤ := fun k => by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    have hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := by
      by_contra! h
      exact hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))
    classical
    let n := Nat.find hex
    have hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M) := by
      have := Nat.find_min hex (show k < n by omega)
      simpa using this
    rw [hpow] at hyk hn
    obtain ⟨y₁, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk
    have hy₁ : y₁ ∉ (x • ⊤ : Submodule R M) := by
      intro h
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
      apply hn
      rw [hk, smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} =
        Submodule.colon (⊥ : Submodule R M) {y₁} := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      constructor
      · intro h
        exact (hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])
      · intro h
        rw [h, smul_zero]
    rw [hcolon]

    set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI
    set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar
    have hybar0 : ybar ≠ 0 := by
      rw [hybar, Ne, Submodule.Quotient.mk_eq_zero]
      exact hy₁
    have hih := ih ybar hybar0 hmem' hrs

    have hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar} := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [hI, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr,
          Submodule.Quotient.mk_zero]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton,
          Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤
        ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)

    have hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton,
        Submodule.mem_bot, mul_smul, smul_comm] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])
    have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x}) := by
      have : Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this]
      exact DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})
    rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) + 1 := by
          gcongr
      _ ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ I) := hd2

/- English proof (translation)
Take `⟨rs, hm, hreg, hdim⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)`. Establish `hann : Module.annihilator B B = ⊥` using `Module.annihilator_eq_bot.mpr inferInstance`. Establish `hP' : P ∈ (Module.annihilator B B).minimalPrimes`. Rewrite using `[hann]`. Conclude with `hP`.

Establish `hA` using `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'`. Take `⟨hprime, y, hy⟩` from `(isAssociatedPrime_iff.mp hA)`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Apply `hprime.ne_top` to reduce the goal to its premises.

Rewrite using `[hy, eq_top_iff]`. Introduce `r _`. Rewrite using `[Submodule.mem_colon_singleton, smul_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hD` using `length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg`.

Rewrite `hD` using `[← hy, ← hdim]`. Conclude with `le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD`.
-/
theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hann : Module.annihilator B B = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hP' : P ∈ (Module.annihilator B B).minimalPrimes := by
    rw [hann]
    exact hP
  have hA := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'
  obtain ⟨hprime, y, hy⟩ := (isAssociatedPrime_iff.mp hA)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  exact le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD

end GroundTheory.Heights₂.Heights
