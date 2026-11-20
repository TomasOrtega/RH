import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiffSmulMem
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcPair

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

abbrev kcBelow (P : Ideal (𝓞 H.E)) : Ideal (𝓞 H.K) := P.comap (algebraMap (𝓞 H.K) (𝓞 H.E))

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [kcBelow, Ideal.mem_comap]`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `hσ' : H.gal σ⁻¹ ∈ φ.Psi`. Rewrite using `[map_inv]`.

Conclude with `inv_mem hσ`. Establish `e : σ⁻¹ • algebraMap (𝓞 H.K) (𝓞 H.E) a = algebraMap (𝓞 H.K) (𝓞 H.E) a`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Use `show σ⁻¹ ((a : H.K) : H.E) = ((a : H.K) : H.E)`. Conclude with `kc_fixK H σ⁻¹ hσ' (a : H.K)`.

Rewrite using `[e]`.
-/
theorem kc_below_smul (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (P : Ideal (𝓞 H.E)) :
    kcBelow H (σ • P) = kcBelow H P := by
  ext a
  simp only [kcBelow, Ideal.mem_comap]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hσ' : H.gal σ⁻¹ ∈ φ.Psi := by
    rw [map_inv]
    exact inv_mem hσ
  have e : σ⁻¹ • algebraMap (𝓞 H.K) (𝓞 H.E) a = algebraMap (𝓞 H.K) (𝓞 H.E) a := by
    apply NumberField.RingOfIntegers.ext
    show σ⁻¹ ((a : H.K) : H.E) = ((a : H.K) : H.E)
    exact kc_fixK H σ⁻¹ hσ' (a : H.K)
  rw [e]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hmax : (span {(p : ℤ)} : Ideal ℤ).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `hmax.eq_of_le (inferInstance : (P.under ℤ).IsPrime).ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Use `show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ P`.

Simplify using `using h`.
-/
private theorem liesOver_span_of_natCast_mem_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (p : ℕ)
    (hp : p.Prime) (h : (p : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  constructor
  have hmax : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine hmax.eq_of_le (inferInstance : (P.under ℤ).IsPrime).ne_top ?_
  rw [Ideal.span_singleton_le_iff_mem]
  show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ P
  simpa using h

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Establish `hn1 : n ≠ 1`. Introduce and unpack `rfl`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hm))`.

Establish `hpm` using `Nat.minFac_prime hn1`. Take `⟨k, hk⟩` from `Nat.minFac_dvd n`. Establish `hm' : (n.minFac : 𝓞 M) * (k : 𝓞 M) ∈ P`. Rewrite using `[← Nat.cast_mul, ← hk]`. Conclude with `hm`.

Break down `hP.mem_or_mem hm' with h | h` into its components or cases. Conclude with `⟨n.minFac, hpm, Nat.minFac_dvd n, liesOver_span_of_natCast_mem_prime P _ hpm h⟩`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hk`.

Conclude with `hn hk`. Establish `hkn : k < n`. Establish `h2` using `hpm.two_le`. Establish `hkpos` using `Nat.pos_of_ne_zero hk0`. Rewrite using `[hk]`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨p, hp, hpk, hl⟩` from `ih k hkn hk0 h`. Conclude with `⟨p, hp, hpk.trans (Dvd.intro_left _ hk.symm), hl⟩`.
-/
theorem kc_exists_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hm : (n : 𝓞 M) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P.LiesOver (span {(p : ℤ)}) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hm))
  have hpm := Nat.minFac_prime hn1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hm' : (n.minFac : 𝓞 M) * (k : 𝓞 M) ∈ P := by
    rw [← Nat.cast_mul, ← hk]
    exact hm
  rcases hP.mem_or_mem hm' with h | h
  · exact ⟨n.minFac, hpm, Nat.minFac_dvd n, liesOver_span_of_natCast_mem_prime P _ hpm h⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hn hk
    have hkn : k < n := by
      have h2 := hpm.two_le
      have hkpos := Nat.pos_of_ne_zero hk0
      rw [hk]
      nlinarith
    obtain ⟨p, hp, hpk, hl⟩ := ih k hkn hk0 h
    exact ⟨p, hp, hpk.trans (Dvd.intro_left _ hk.symm), hl⟩

/- English proof (translation)
Apply `H.gal.injective` to reduce the goal to its premises. Rewrite using `[map_mul, kc_gal_conj, map_one]`. Apply the tactic sequence `ext <;> simp [Frame.cc, c0]`.
-/
theorem kc_conj_sq : H.conj * H.conj = 1 := by
  apply H.gal.injective
  rw [map_mul, kc_gal_conj, map_one]
  ext <;> simp [Frame.cc, c0]

variable (C : HostCore H)
include C

/- English proof (translation)
Introduce `P hP hdvd`. Use `H.galois` as an intermediate fact. Assume the negation of the conclusion as `hnot`. Use `kc_not_dvd_different H.K H.E P ?_ hdvd` and prove the remaining obligations. Introduce `hbot σ hσ`.

Establish `hn0 : Ideal.absNorm P ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Take `⟨l, hl, -, hlo⟩` from `kc_exists_prime P (Ideal.absNorm P) hn0 (Ideal.absNorm_mem P)`. Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `hlP : (l : 𝓞 H.E) ∈ P`. Establish `h1 : (l : ℤ) ∈ P.under ℤ`.

Rewrite using `[← hlo.over]`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify using `using h1`. Establish `hlq : ¬ l ∣ H.QS * H.q`. Introduce and unpack `⟨m, hm⟩`.

Apply `hnot` to reduce the goal to its premises. Rewrite using `[hm, Nat.cast_mul]`. Conclude with `P.mul_mem_right _ hlP`. Take `⟨u, hu, hgal⟩` from `(C.inertia l P (σ.restrictScalars ℚ)).mp fun x => hσ x`. Establish `hmod : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q]` using `Nat.ModEq.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd (Dvd.intro _ rfl) hlq) hu`.

Break down `H.art_d u hmod with h1 | h1` into its components or cases. Establish `h2 : σ.restrictScalars ℚ = 1` using `H.gal.injective (by rw [hgal, h1, map_one])`. Use extensionality with `x`. Conclude with `congrArg (fun τ : H.E ≃ₐ[ℚ] H.E => τ x) h2`. It suffices to derive a contradiction.

Establish `hpsi` using `kc_restrict_mem_Psi H σ`. Rewrite `hpsi` using `[hgal, h1]`. Conclude with `kc_iod_not_mem hpsi`.
-/
theorem diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P := by
  intro P hP hdvd
  have := H.galois
  by_contra hnot
  refine kc_not_dvd_different H.K H.E P ?_ hdvd
  intro hbot σ hσ
  have hn0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨l, hl, -, hlo⟩ := kc_exists_prime P (Ideal.absNorm P) hn0 (Ideal.absNorm_mem P)
  have : Fact l.Prime := ⟨hl⟩
  have hlP : (l : 𝓞 H.E) ∈ P := by
    have h1 : (l : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hlq : ¬ l ∣ H.QS * H.q := by
    rintro ⟨m, hm⟩
    apply hnot
    rw [hm, Nat.cast_mul]
    exact P.mul_mem_right _ hlP
  obtain ⟨u, hu, hgal⟩ := (C.inertia l P (σ.restrictScalars ℚ)).mp fun x => hσ x
  have hmod : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    Nat.ModEq.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd (Dvd.intro _ rfl) hlq) hu
  rcases H.art_d u hmod with h1 | h1
  · have h2 : σ.restrictScalars ℚ = 1 := H.gal.injective (by rw [hgal, h1, map_one])
    ext x
    exact congrArg (fun τ : H.E ≃ₐ[ℚ] H.E => τ x) h2
  · exfalso
    have hpsi := kc_restrict_mem_Psi H σ
    rw [hgal, h1] at hpsi
    exact kc_iod_not_mem hpsi

/- English proof (translation)
Use `H.galois` as an intermediate fact. Introduce `heq`. Establish `hn0 : H.QS * H.q ≠ 0` using `Nat.mul_ne_zero H.QS_pos.ne' (by`. Introduce and unpack `h0`. Use `H.QS_coprime` as an intermediate fact.

Rewrite `this` using `[h0, zero_mul, Nat.coprime_zero_right]`. Establish `h2` using `kc_two_dvd H`. Rewrite `h2` using `[this]`. Use the proof step `omega)`. Take `⟨l, hl, hldvd, hlo⟩` from `kc_exists_prime P (H.QS * H.q) hn0 hm`.

Establish `: P.LiesOver (kcBelow H P)` using `⟨rfl⟩`. Establish `: (H.conj • P).LiesOver (kcBelow H P)` using `⟨heq⟩`. Take `⟨τ, hτ⟩` from `exists_smul_eq_of_isGaloisGroup (kcBelow H P) P (H.conj • P) (H.E ≃ₐ[H.K] H.E)`. Establish `hτ' : (τ.restrictScalars ℚ) • P = H.conj • P` using `hτ`. Establish `hst : (τ.restrictScalars ℚ)⁻¹ * H.conj ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P`.

Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul, ← hτ', inv_smul_smul]`. Establish `hpsi` using `C.decomp_typeI l hl hldvd P _ hst`. Rewrite `hpsi` using `[map_mul, map_inv, Subgroup.mul_mem_cancel_left _ (inv_mem (kc_restrict_mem_Psi H τ)), kc_gal_conj]`. Conclude with `kc_cc_not_mem hpsi`.
-/
theorem kc_below_ne (P : Ideal (𝓞 H.E)) [P.IsPrime] (hm : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P) :
    kcBelow H P ≠ kcBelow H (H.conj • P) := by
  have := H.galois
  intro heq
  have hn0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' (by
    rintro h0
    have := H.QS_coprime
    rw [h0, zero_mul, Nat.coprime_zero_right] at this
    have h2 := kc_two_dvd H
    rw [this] at h2
    omega)
  obtain ⟨l, hl, hldvd, hlo⟩ := kc_exists_prime P (H.QS * H.q) hn0 hm
  have : P.LiesOver (kcBelow H P) := ⟨rfl⟩
  have : (H.conj • P).LiesOver (kcBelow H P) := ⟨heq⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup (kcBelow H P) P (H.conj • P) (H.E ≃ₐ[H.K] H.E)
  have hτ' : (τ.restrictScalars ℚ) • P = H.conj • P := hτ
  have hst : (τ.restrictScalars ℚ)⁻¹ * H.conj ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hτ', inv_smul_smul]
  have hpsi := C.decomp_typeI l hl hldvd P _ hst
  rw [map_mul, map_inv, Subgroup.mul_mem_cancel_left _ (inv_mem (kc_restrict_mem_Psi H τ)),
    kc_gal_conj] at hpsi
  exact kc_cc_not_mem hpsi

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- English proof (translation)
Use `H.galois` as an intermediate fact. Take `⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, f I = H.conj • I` from `⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv, fun _ => rfl⟩`. Establish `hD0 : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hfD : f (differentIdeal (𝓞 H.K) (𝓞 H.E)) = differentIdeal (𝓞 H.K) (𝓞 H.E)`. Rewrite using `[hf]`.

Conclude with `kc_diff_smul_eq H H.conj`. Establish `hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I` using `fun I => by`. Rewrite using `[← mul_smul, kc_conj_sq, one_smul]`. Set `p : Ideal (𝓞 H.E) → Prop` to `fun P => WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))`. Establish `hp : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (differentIdeal (𝓞 H.K) (𝓞 H.E)), (p (f P) ↔ ¬ p P)`.

Introduce `P hP`. Establish `hPp : P.IsPrime` using `Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)`. Establish `hPd : P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E)` using `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP`. Establish `hne` using `kc_below_ne H C P (diffSupport H C P hPp hPd)`. Use `show WellOrderingRel (kcBelow H (f P)) (kcBelow H (H.conj • f P)) ↔ ¬ WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))`.

Rewrite using `[hf, hcc]`. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Conclude with `asymm h1 h2`. Introduce `h1`.

Break down `trichotomous_of WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P)) with h | h | h` into its components or cases. Conclude with `absurd h h1`. Conclude with `absurd h hne`. Conclude with `h`. Take `⟨B, hB, -, hBtop, hinv, -⟩` from `kc_pairing _ hD0 f hfD p hp`.

Use `⟨B, ?_, ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf]`. Conclude with `hB`. Rewrite using `[← hf]`. Conclude with `hBtop`.

Take `⟨g, hg⟩ : ∃ g : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, g I = σ • I` from `⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) σ).toMulEquiv, fun _ => rfl⟩`. Rewrite using `[← hg]`. Use `hinv g (by rw [hg]; exact kc_diff_smul_eq H σ) fun P _ => ?_` and prove the remaining obligations. Establish `hn : H.gal (H.conj * σ * H.conj⁻¹) ∈ φ.Psi`. Establish `hσ' : φ.chD (H.gal σ) = 1` using `hσ`.

Use `show φ.chD (H.gal (H.conj * σ * H.conj⁻¹)) = 1`. Simplify using `only [map_mul, map_inv, hσ', mul_one, mul_inv_cancel]`. Establish `e1 : (H.conj * σ * H.conj⁻¹) • H.conj • P = H.conj • σ • P`. Rewrite using `[← mul_smul, inv_mul_cancel_right, mul_smul]`. Use `show WellOrderingRel (kcBelow H (g P)) (kcBelow H (H.conj • g P)) ↔ WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))`.

Rewrite using `[hg, kc_below_smul H σ hσ P, ← e1, kc_below_smul H _ hn]`.
-/
theorem principal : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟 := by
  have := H.galois
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, f I = H.conj • I :=
    ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv, fun _ => rfl⟩
  have hD0 : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hfD : f (differentIdeal (𝓞 H.K) (𝓞 H.E)) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
    rw [hf]
    exact kc_diff_smul_eq H H.conj
  have hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := fun I => by
    rw [← mul_smul, kc_conj_sq, one_smul]
  let p : Ideal (𝓞 H.E) → Prop := fun P =>
    WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
  have hp : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (differentIdeal (𝓞 H.K) (𝓞 H.E)),
      (p (f P) ↔ ¬ p P) := by
    intro P hP
    have hPp : P.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    have hPd : P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hne := kc_below_ne H C P (diffSupport H C P hPp hPd)
    show WellOrderingRel (kcBelow H (f P)) (kcBelow H (H.conj • f P)) ↔
      ¬ WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hf, hcc]
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P)) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  obtain ⟨B, hB, -, hBtop, hinv, -⟩ := kc_pairing _ hD0 f hfD p hp
  refine ⟨B, ?_, ?_, fun σ hσ => ?_⟩
  · rw [← hf]
    exact hB
  · rw [← hf]
    exact hBtop
  · obtain ⟨g, hg⟩ : ∃ g : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, g I = σ • I :=
      ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) σ).toMulEquiv, fun _ => rfl⟩
    rw [← hg]
    refine hinv g (by rw [hg]; exact kc_diff_smul_eq H σ) fun P _ => ?_
    have hn : H.gal (H.conj * σ * H.conj⁻¹) ∈ φ.Psi := by
      have hσ' : φ.chD (H.gal σ) = 1 := hσ
      show φ.chD (H.gal (H.conj * σ * H.conj⁻¹)) = 1
      simp only [map_mul, map_inv, hσ', mul_one, mul_inv_cancel]
    have e1 : (H.conj * σ * H.conj⁻¹) • H.conj • P = H.conj • σ • P := by
      rw [← mul_smul, inv_mul_cancel_right, mul_smul]
    show WellOrderingRel (kcBelow H (g P)) (kcBelow H (H.conj • g P)) ↔
      WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hg, kc_below_smul H σ hσ P, ← e1, kc_below_smul H _ hn]

/- English proof (translation)
Use `C.cm` as an intermediate fact. Establish `hdiff : differentIdeal (𝓞 H.F) (𝓞 H.E) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hPmax, hle⟩` from `Ideal.exists_le_maximal _ hne`. Use `kc_not_dvd_different H.F H.E P ?_ (Ideal.dvd_iff_le.mpr hle)` and prove the remaining obligations.

Introduce `hbot σ hσ`. Establish `hmem : σ ∈ Subgroup.zpowers (IsCMField.complexConj H.E)`. Rewrite using `[IsCMField.zpowers_complexConj_eq_top]`. Conclude with `Subgroup.mem_top σ`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hmem`.

Establish `h2 : k % (orderOf (IsCMField.complexConj H.E) : ℤ) = k % 2`. Rewrite using `[IsCMField.orderOf_complexConj]`. Both sides reduce to the same expression. Rewrite `hσ`, the goal using `[← zpow_mod_orderOf, h2]`. Break down `Int.emod_two_eq_zero_or_one k with hk | hk` into its components or cases.

Rewrite using `[hk, zpow_zero]`. It suffices to derive a contradiction. Rewrite `hσ` using `[hk, zpow_one]`. Conclude with `kc_unr H C P hPmax.isPrime hbot hσ`. Establish `h` using `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.F (𝓞 H.F) H.E (𝓞 H.E)`.

Rewrite `h` using `[hdiff, Ideal.absNorm_top, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two]`. Establish `hsign : (discr H.E).sign = 1`. Rewrite using `[sign_discr]`. Establish `h1` using `IsTotallyComplex.finrank H.E`. Rewrite `h1` using `[C.finrank_E]`.

Establish `h3 : NumberField.InfinitePlace.nrComplexPlaces H.E = 2 * φ.ord` using `by omega`. Rewrite using `[h3, pow_mul, neg_one_sq, one_pow]`. Rewrite using `[← Int.sign_mul_natAbs (discr H.E), hsign, one_mul, h, Nat.cast_pow, Int.natAbs_sq]`.
-/
theorem discr_sq : discr H.E = discr H.F ^ 2 := by
  have := C.cm
  have hdiff : differentIdeal (𝓞 H.F) (𝓞 H.E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    refine kc_not_dvd_different H.F H.E P ?_ (Ideal.dvd_iff_le.mpr hle)
    intro hbot σ hσ
    have hmem : σ ∈ Subgroup.zpowers (IsCMField.complexConj H.E) := by
      rw [IsCMField.zpowers_complexConj_eq_top]
      exact Subgroup.mem_top σ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : k % (orderOf (IsCMField.complexConj H.E) : ℤ) = k % 2 := by
      rw [IsCMField.orderOf_complexConj]
      rfl
    rw [← zpow_mod_orderOf, h2] at hσ ⊢
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk, zpow_zero]
    · exfalso
      rw [hk, zpow_one] at hσ
      exact kc_unr H C P hPmax.isPrime hbot hσ
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.F (𝓞 H.F) H.E (𝓞 H.E)
  rw [hdiff, Ideal.absNorm_top, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  have hsign : (discr H.E).sign = 1 := by
    rw [sign_discr]
    have h1 := IsTotallyComplex.finrank H.E
    rw [C.finrank_E] at h1
    have h3 : NumberField.InfinitePlace.nrComplexPlaces H.E = 2 * φ.ord := by omega
    rw [h3, pow_mul, neg_one_sq, one_pow]
  rw [← Int.sign_mul_natAbs (discr H.E), hsign, one_mul, h, Nat.cast_pow, Int.natAbs_sq]

end Formalism.HC.Der

end
