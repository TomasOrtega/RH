import Mathlib
import Formalism.PairingDivisors.StatementN

noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals

variable {F : Type} [Field F] [NumberField F]

abbrev IdealsIn (C : ClassGroup (𝓞 F)) : Type := {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}

def IsClassZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : IdealsIn C => ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)

def IsZetaValues (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

def denomExp (l : ℕ) (r : ℚ) : ℕ := (-padicValRat l r).toNat

def cE (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : ℕ :=
  Finset.univ.sup fun C => denomExp l (z C / 2 ^ finrank ℚ F)

def mMin (l n : ℕ) : ℕ := sInf {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)}

def LocalBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (l : ℕ) : Prop :=
  cE z l ≤ finrank ℚ F * padicValNat l 2 + mMin l (finrank ℚ F * k) ∧
  (l ≠ 2 → ¬ (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 0) ∧
  (l ≠ 2 → (l - 1) ∣ finrank ℚ F * k → mMin l (finrank ℚ F * k) = 1 + padicValNat l (finrank ℚ F * k)) ∧
  (l = 2 → mMin l (finrank ℚ F * k) = 2 + padicValNat 2 (finrank ℚ F * k))

def SumBound (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)).Finite ∧
  ∑ᶠ l : Nat.Primes, (cE z l : ℝ) * Real.log (l : ℕ) ≤
    ((finrank ℚ F * k : ℕ) : ℝ) * Real.log (((finrank ℚ F * k : ℕ) : ℝ) + 1)

def DenomAt (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop :=
  (∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z) ∧
  ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z →
    (∀ l : ℕ, l.Prime → LocalBound k z l) ∧ (16 ≤ finrank ℚ F * k → SumBound k z)

def ZetaDenominators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : ℕ), 1 ≤ s → DenomAt (maximalRealSubfield E) (2 * s)

def ZetaDenominatorsReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ), 1 ≤ s → DenomAt F (2 * s)

/- English proof (translation)
Introduce `E _ _ _ s hs` and use `h (maximalRealSubfield E) s hs`.
-/
theorem ZetaDenominatorsReal.cm (h : ZetaDenominatorsReal) : ZetaDenominators :=
  fun E _ _ _ s hs => h (maximalRealSubfield E) s hs

/- English proof (translation)
Establish `ho : IsOpen ({1}ᶜ : Set ℂ)` using `isOpen_compl_singleton`. Establish `hc : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected`. Use `(h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_` and prove the remaining obligations. Establish `ho' : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [ho'.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs`.

Conclude with `(h.2 s hs).unique (h'.2 s hs)`.
-/
theorem IsClassZeta.eqOn {C : ClassGroup (𝓞 F)} {Z Z' : ℂ → ℂ} (h : IsClassZeta C Z) (h' : IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_
  have ho' : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho'.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

/- English proof (translation)
Use function extensionality and compare the values at `C`. Take `⟨Z, hZ, e⟩` from `h C`. Take `⟨Z', hZ', e'⟩` from `h' C`. Establish `hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ)`. Establish `: (k : ℂ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`.

Simplify using `using this`. Use `hZ.eqOn hZ' hne` as an intermediate fact. Rewrite `this` using `[e, e']`. Conclude with `this` after adjusting the coercions.
-/
theorem IsZetaValues.unique {k : ℕ} (hk : 1 ≤ k) {z z' : ClassGroup (𝓞 F) → ℚ} (h : IsZetaValues k z)
    (h' : IsZetaValues k z') : z = z' := by
  funext C
  obtain ⟨Z, hZ, e⟩ := h C
  obtain ⟨Z', hZ', e'⟩ := h' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have := hZ.eqOn hZ' hne
  rw [e, e'] at this
  exact_mod_cast this

/- English proof (translation)
The claim follows from `Nat.sInf_mem (s := {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)}) ⟨_, l + 1, by omega, by simp, rfl⟩`.
-/
theorem mMin_mem {l : ℕ} (hl : 1 ≤ l) (n : ℕ) : ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ mMin l n = padicValNat l (a ^ n - 1) :=
  Nat.sInf_mem (s := {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)})
    ⟨_, l + 1, by omega, by simp, rfl⟩

/- English proof (translation)
Unfold `Formalism.PairingDivisionLocalBalance.mE`. Use `split_ifs with h1 h2`. Conclude with `h.2.2.2 h1`. Conclude with `h.2.2.1 h1 h2`. Conclude with `h.2.1 h1 h2`.
-/
theorem LocalBound.mMin_eq {k : ℕ} {z : ClassGroup (𝓞 F) → ℚ} {l : ℕ} (h : LocalBound k z l) :
    mMin l (finrank ℚ F * k) = Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k) := by
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h1 h2
  · exact h.2.2.2 h1
  · exact h.2.2.1 h1 h2
  · exact h.2.1 h1 h2

/- English proof (translation)
Establish `h2 : padicValNat 2 24 = 3`. Rewrite using `[show 24 = 2 ^ 3 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]`. Establish `h3 : padicValNat 3 24 = 1`. Rewrite using `[show 24 = 3 ^ 1 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]`. Establish `hn : (-1 / 24 : ℚ).num = -1` using `by norm_num`.

Establish `hd : (-1 / 24 : ℚ).den = 24` using `by norm_num`. Use `⟨?_, ?_, by simp [denomExp]⟩` and prove the remaining obligations. Simplify using `only [denomExp, padicValRat, hn, hd, h2]`. Simplify using `[padicValInt]`. Simplify using `only [denomExp, padicValRat, hn, hd, h3]`.

Simplify using `[padicValInt]`.
-/
example : denomExp 2 (-1 / 24) = 3 ∧ denomExp 3 (-1 / 24) = 1 ∧ denomExp 2 0 = 0 := by
  have h2 : padicValNat 2 24 = 3 := by
    rw [show 24 = 2 ^ 3 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h3 : padicValNat 3 24 = 1 := by
    rw [show 24 = 3 ^ 1 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hn : (-1 / 24 : ℚ).num = -1 := by norm_num
  have hd : (-1 / 24 : ℚ).den = 24 := by norm_num
  refine ⟨?_, ?_, by simp [denomExp]⟩
  · simp only [denomExp, padicValRat, hn, hd, h2]; simp [padicValInt]
  · simp only [denomExp, padicValRat, hn, hd, h3]; simp [padicValInt]

/- English proof (translation)
The claim follows from `IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective`.
-/
theorem pir_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton, show (n : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (n : ℤ) by simp, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using the standard rewrite rules.
-/
theorem absNorm_span_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_singleton, show (n : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (n : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank]
  simp

/- English proof (translation)
Use `haveI := pir_rat`. Take `⟨a, rfl⟩ : ∃ a, I = Ideal.span {a}` from `⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩`. Take `⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ)` from `⟨Rat.ringOfIntegersEquiv a, by`. Apply `Rat.ringOfIntegersEquiv.injective` to reduce the goal to its premises. Use the proof step `simp⟩`.

Use `⟨m.natAbs, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq m with h | h` into its components or cases. Rewrite using `[h]`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [h]`.

Rewrite using `[Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]`.
-/
theorem exists_span_rat (I : Ideal (𝓞 ℚ)) : ∃ n : ℕ, I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI := pir_rat
  obtain ⟨a, rfl⟩ : ∃ a, I = Ideal.span {a} := ⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ) := ⟨Rat.ringOfIntegersEquiv a, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  refine ⟨m.natAbs, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]

/- English proof (translation)
Use `⟨fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hs0 : s ≠ 0` using `by rintro rfl; norm_num at hs`. Use `haveI := pir_rat`. Use `haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := (@Fintype.card_le_one_iff_subsingleton _ instFintypeClassGroupOfIsPrincipalIdealRing).1 (card_classGroup_eq_one (R := 𝓞 ℚ)).le`. Set `g : IdealsIn C → ℕ` to `fun I => Ideal.absNorm (I.1 : Ideal (𝓞 ℚ))`.

Establish `hg : Function.Injective g` using `fun I J h => by`. Take `⟨n, hn⟩` from `exists_span_rat (I.1 : Ideal (𝓞 ℚ))`. Take `⟨m, hm⟩` from `exists_span_rat (J.1 : Ideal (𝓞 ℚ))`. Simplify using `only [g, hn, hm, absNorm_span_rat] at h`. Conclude with `Subtype.ext (Subtype.ext (by rw [hn, hm, h]))`.

Establish `hr : ∀ n ∉ Set.range g, (n : ℂ) ^ (-s) = 0` using `fun n hn => by`. Distinguish the cases in `h0 : n = 0`. Simplify using `[h0, hs0]`. Use `(hn ⟨⟨⟨Ideal.span {(n : 𝓞 ℚ)}, mem_nonZeroDivisors_of_ne_zero ?_⟩, Subsingleton.elim _ _⟩, absNorm_span_rat n⟩).elim` and prove the remaining obligations. Simplify using `using h0`.

Use `(hg.hasSum_iff (f := fun n : ℕ => (n : ℂ) ^ (-s)) hr).2 ?_` and prove the remaining obligations. Rewrite using `[zeta_eq_tsum_one_div_nat_cpow hs]`. Simplify `(Complex.summable_one_div_nat_cpow.2 hs).hasSum` using `only [Complex.cpow_neg, one_div]`.
-/
theorem isClassZeta_rat (C : ClassGroup (𝓞 ℚ)) : IsClassZeta C riemannZeta := by
  refine ⟨fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  haveI := pir_rat
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    (@Fintype.card_le_one_iff_subsingleton _ instFintypeClassGroupOfIsPrincipalIdealRing).1
      (card_classGroup_eq_one (R := 𝓞 ℚ)).le
  let g : IdealsIn C → ℕ := fun I => Ideal.absNorm (I.1 : Ideal (𝓞 ℚ))
  have hg : Function.Injective g := fun I J h => by
    obtain ⟨n, hn⟩ := exists_span_rat (I.1 : Ideal (𝓞 ℚ))
    obtain ⟨m, hm⟩ := exists_span_rat (J.1 : Ideal (𝓞 ℚ))
    simp only [g, hn, hm, absNorm_span_rat] at h
    exact Subtype.ext (Subtype.ext (by rw [hn, hm, h]))
  have hr : ∀ n ∉ Set.range g, (n : ℂ) ^ (-s) = 0 := fun n hn => by
    by_cases h0 : n = 0
    · simp [h0, hs0]
    · refine (hn ⟨⟨⟨Ideal.span {(n : 𝓞 ℚ)}, mem_nonZeroDivisors_of_ne_zero ?_⟩, Subsingleton.elim _ _⟩,
        absNorm_span_rat n⟩).elim
      simpa using h0
  refine (hg.hasSum_iff (f := fun n : ℕ => (n : ℂ) ^ (-s)) hr).2 ?_
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simpa only [Complex.cpow_neg, one_div] using (Complex.summable_one_div_nat_cpow.2 hs).hasSum

/- English proof (translation)
Introduce `C` and use `⟨_, isClassZeta_rat C, by have h := riemannZeta_neg_nat_eq_bernoulli 1 have hb : bernoulli 2 = 1 / 6 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two] rw [show (1 + 1 : ℕ) = 2 from rfl, hb] at h rw [show (1 - ((2 : ℕ) : ℂ)) = -((1 : ℕ) : ℂ) by norm_num, h] …`.
-/
example : IsZetaValues (F := ℚ) 2 (fun _ => -1 / 12) := fun C => ⟨_, isClassZeta_rat C, by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  have hb : bernoulli 2 = 1 / 6 := by rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two]
  rw [show (1 + 1 : ℕ) = 2 from rfl, hb] at h
  rw [show (1 - ((2 : ℕ) : ℂ)) = -((1 : ℕ) : ℂ) by norm_num, h]
  norm_num⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
