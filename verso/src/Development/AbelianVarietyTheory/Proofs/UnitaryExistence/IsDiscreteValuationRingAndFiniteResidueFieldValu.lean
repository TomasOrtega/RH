import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open IsLocalRing NumberField IsDedekindDomain

namespace GlobalTheory

open IsLocalRing IsDedekindDomain NumberField in

/- English proof (translation)
Set `S` to `Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors`. Use `haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField K _ _`. Establish `hD : IsDiscreteValuationRing S` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S`. Use `haveI : IsLocalRing S := inferInstance`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`.

Establish `hS : Finite (ResidueField S)` using `Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal S).toEquiv`. Conclude with `⟨hD, hS⟩`.
-/
theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (hfin : Finite (R ⧸ v.asIdeal)) :
      IsDiscreteValuationRing ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ∧
        Finite (IsLocalRing.ResidueField
          ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)) := by
  let S := Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField K _ _
  have hD : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  haveI : IsLocalRing S := inferInstance
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hS : Finite (ResidueField S) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal S).toEquiv
  exact ⟨hD, hS⟩

open IsLocalRing IsDedekindDomain NumberField in
/- English proof (translation)
Establish `hmem : ∀ (B : ValuationSubring K) (hB : A ≤ B) (x : A), x ∈ A.idealOfLE B hB ↔ (x : K) ∈ B.nonunits`. Introduce `B hB x`. Rewrite using `[ValuationSubring.mem_nonunits_iff]`. Unfold `ValuationSubring.idealOfLE`. Rewrite using `[Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]`.

Both sides reduce to the same expression. Establish `hmax : ∀ (B : ValuationSubring K) (hB : A ≤ B), (a : K) ∈ B.nonunits → A.idealOfLE B hB = maximalIdeal A`. Introduce `B hB haB`. Establish `hne : A.idealOfLE B hB ≠ ⊥`. Introduce `hbot`.

Establish `: a ∈ A.idealOfLE B hB` using `(hmem B hB a).2 haB`. Rewrite `this` using `[hbot, Ideal.mem_bot]`. Conclude with `ha0 this`. Use `(inferInstance : (A.idealOfLE B hB).IsPrime).isMaximal hne` as an intermediate fact. Conclude with `IsLocalRing.eq_maximalIdeal this`.

Establish `haA : (a : K) ∈ A.nonunits` using `(ValuationSubring.nonunits_le_nonunits.2 h) haW`. Establish `hcongr : ∀ (P Q : Ideal A) [P.IsPrime] [Q.IsPrime], P = Q → A.ofPrime P = A.ofPrime Q`. Introduce and unpack `P Q _ _ rfl`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem eq_of_le_of_mem_nonunits_of_dvr {K : Type*} [Field K]
    (A W : ValuationSubring K) (h : A ≤ W) [IsDiscreteValuationRing A]
    (a : A) (ha0 : a ≠ 0) (haW : (a : K) ∈ W.nonunits) : A = W := by
  have hmem : ∀ (B : ValuationSubring K) (hB : A ≤ B) (x : A),
      x ∈ A.idealOfLE B hB ↔ (x : K) ∈ B.nonunits := by
    intro B hB x
    rw [ValuationSubring.mem_nonunits_iff]
    unfold ValuationSubring.idealOfLE
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hmax : ∀ (B : ValuationSubring K) (hB : A ≤ B), (a : K) ∈ B.nonunits →
      A.idealOfLE B hB = maximalIdeal A := by
    intro B hB haB
    have hne : A.idealOfLE B hB ≠ ⊥ := by
      intro hbot
      have : a ∈ A.idealOfLE B hB := (hmem B hB a).2 haB
      rw [hbot, Ideal.mem_bot] at this
      exact ha0 this
    have := (inferInstance : (A.idealOfLE B hB).IsPrime).isMaximal hne
    exact IsLocalRing.eq_maximalIdeal this
  have haA : (a : K) ∈ A.nonunits := (ValuationSubring.nonunits_le_nonunits.2 h) haW
  have hcongr : ∀ (P Q : Ideal A) [P.IsPrime] [Q.IsPrime], P = Q → A.ofPrime P = A.ofPrime Q := by
    rintro P Q _ _ rfl; rfl
  calc A = A.ofPrime (A.idealOfLE A le_rfl) := (A.ofPrime_idealOfLE A le_rfl).symm
    _ = A.ofPrime (A.idealOfLE W h) := hcongr _ _ ((hmax A le_rfl haA).trans (hmax W h haW).symm)
    _ = W := A.ofPrime_idealOfLE W h

open IsLocalRing IsDedekindDomain NumberField in

/- English proof (translation)
Establish `hnW` using `hW`. Establish `hint : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ W`. Introduce `x`. Establish `h : IsIntegral W (x : L)` using `(RingOfIntegers.isIntegral_coe x).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`.

Use `show (x : L) ∈ W`. Rewrite using `[← hy]`. Conclude with `y.2`. Set `f : 𝓞 L →+* W` to `(algebraMap (𝓞 L) L).codRestrict W hint`. Establish `hf : ∀ x : 𝓞 L, ((f x : W) : L) = (x : L)` using `fun x => rfl`.

Set `P : Ideal (𝓞 L)` to `(maximalIdeal W).comap f`. Establish `hPmem : ∀ x : 𝓞 L, x ∈ P ↔ (x : L) ∈ W.nonunits`. Introduce `x`. Rewrite using `[Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff, hf]`. Establish `hnP : (n : 𝓞 L) ∈ P`.

Rewrite using `[hPmem]`. Simplify using `using hnW`. Establish `hPne : P ≠ ⊥`. Introduce `hbot`. Rewrite `hnP` using `[hbot, Ideal.mem_bot]`.

Conclude with `hn (by exact_mod_cast hnP)`. Set `v : HeightOneSpectrum (𝓞 L)` to `⟨P, Ideal.comap_isPrime f (maximalIdeal W), hPne⟩`. Establish `hfin : Finite (𝓞 L ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hPne`. Set `A` to `HeightOneSpectrum.valuationSubringAtPrime L v`. Establish `hAW : A ≤ W`.

Introduce `x hx`. Set `S` to `Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors`. Use `haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField L _ _`. Take `⟨⟨a, s⟩, hy⟩` from `IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : S)`. Establish `hspec` using `congrArg Subtype.val (IsLocalization.mk'_spec S a s)`.

Simplify using `only at hy`. Rewrite `hspec` using `[hy]`. Express the relevant statement in the definitionally equal form `x * ((s : 𝓞 L) : L) = (a : L) at hspec`. Establish `hsu : IsUnit (f s)`. Assume the negation of the conclusion as `hns`.

Conclude with `s.2 (show (s : 𝓞 L) ∈ P from (IsLocalRing.mem_maximalIdeal _).2 hns)`. Take `⟨t, ht⟩` from `hsu.exists_right_inv`. Establish `h1 : ((s : 𝓞 L) : L) * (t : L) = 1`. Rewrite using `[← hf]`. Conclude with `congrArg Subtype.val ht`.

Establish `hx' : x = (a : L) * (t : L)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx']`. Conclude with `mul_mem (hint a) t.2`. Take `⟨hD, hF⟩` from `_root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime L v hfin`.

Establish `hnA : (n : L) ∈ A` using `natCast_mem A n`. Establish `heq : A = W` using `eq_of_le_of_mem_nonunits_of_dvr A W hAW ⟨(n : L), hnA⟩ (by`. Introduce `h0`. Use `congrArg Subtype.val h0` as an intermediate fact. Simplify using `only [ZeroMemClass.coe_zero] at this`.

Conclude with `hn (by exact_mod_cast this)) hnW`. Rewrite using `[← heq]`. Conclude with `⟨hD, hF⟩`.
-/
theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField {L : Type*} [Field L]
    [NumberField L] (W : ValuationSubring L) {n : ℕ} (hn : n ≠ (0 : ℕ))
    (hW : (↑n : L) ∈ W.nonunits) :
      IsDiscreteValuationRing ↥W ∧ Finite (IsLocalRing.ResidueField ↥W) := by
  have hnW := hW
  have hint : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ W := by
    intro x
    have h : IsIntegral W (x : L) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    show (x : L) ∈ W
    rw [← hy]; exact y.2
  let f : 𝓞 L →+* W := (algebraMap (𝓞 L) L).codRestrict W hint
  have hf : ∀ x : 𝓞 L, ((f x : W) : L) = (x : L) := fun x => rfl
  let P : Ideal (𝓞 L) := (maximalIdeal W).comap f
  have hPmem : ∀ x : 𝓞 L, x ∈ P ↔ (x : L) ∈ W.nonunits := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff, hf]
  have hnP : (n : 𝓞 L) ∈ P := by
    rw [hPmem]; simpa using hnW
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hnP
    exact hn (by exact_mod_cast hnP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime f (maximalIdeal W), hPne⟩
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  let A := HeightOneSpectrum.valuationSubringAtPrime L v
  have hAW : A ≤ W := by
    intro x hx
    let S := Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField L _ _
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : S)
    have hspec := congrArg Subtype.val (IsLocalization.mk'_spec S a s)
    simp only at hy
    rw [hy] at hspec
    change x * ((s : 𝓞 L) : L) = (a : L) at hspec
    have hsu : IsUnit (f s) := by
      by_contra hns
      exact s.2 (show (s : 𝓞 L) ∈ P from (IsLocalRing.mem_maximalIdeal _).2 hns)
    obtain ⟨t, ht⟩ := hsu.exists_right_inv
    have h1 : ((s : 𝓞 L) : L) * (t : L) = 1 := by
      rw [← hf]; exact congrArg Subtype.val ht
    have hx' : x = (a : L) * (t : L) := by
      calc x = x * (((s : 𝓞 L) : L) * (t : L)) := by rw [h1, mul_one]
        _ = (a : L) * (t : L) := by rw [← mul_assoc, hspec]
    rw [hx']
    exact mul_mem (hint a) t.2
  obtain ⟨hD, hF⟩ :=
    _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime L v hfin
  have hnA : (n : L) ∈ A := natCast_mem A n
  have heq : A = W := eq_of_le_of_mem_nonunits_of_dvr A W hAW ⟨(n : L), hnA⟩
    (by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero] at this
      exact hn (by exact_mod_cast this)) hnW
  rw [← heq]
  exact ⟨hD, hF⟩

end GlobalTheory
