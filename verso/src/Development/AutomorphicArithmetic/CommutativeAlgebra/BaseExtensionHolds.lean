import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardPow

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory

/- English proof (translation)
Establish `hk : I = RingHom.ker f`. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker]`. Conclude with `h a`. Conclude with `Nat.card_congr ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv`.
-/
private theorem card_quot_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (h : ∀ a, a ∈ I ↔ f a = 0) :
    Nat.card (A ⧸ I) = Nat.card B := by
  have hk : I = RingHom.ker f := by
    ext a
    rw [RingHom.mem_ker]
    exact h a
  exact Nat.card_congr ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

section Local

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

private def iota : 𝓞 E →+* Gal.Int.Geo.Ow w :=
  (algebraMap (𝓞 E) E).codRestrict (w.valuation E).valuationSubring
    (fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one a)

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.valuationSubring.integers (w.valuation E)).isUnit_iff_valuation_eq_one, ← w.valuation_lt_one_iff_mem (K := E) a]`. Conclude with `⟨fun h => lt_of_le_of_ne (w.valuation_le_one a) h, ne_of_lt⟩`.
-/
private theorem iota_mem_max (a : 𝓞 E) :
    iota w a ∈ IsLocalRing.maximalIdeal (Gal.Int.Geo.Ow w) ↔ a ∈ w.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.valuationSubring.integers (w.valuation E)).isUnit_iff_valuation_eq_one,
    ← w.valuation_lt_one_iff_mem (K := E) a]
  exact ⟨fun h => lt_of_le_of_ne (w.valuation_le_one a) h, ne_of_lt⟩

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Establish `hx : (x : E) ∈ w.valuationSubringAtPrime E`. Rewrite using `[HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`. Conclude with `x.2`.

Use `haveI : IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime E) := Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors`. Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj w.asIdeal.primeCompl (⟨x, hx⟩ : w.valuationSubringAtPrime E)`. Establish `hxs : x * iota w (s : 𝓞 E) = iota w a` using `Subtype.ext (congrArg (fun z : w.valuationSubringAtPrime E => (z : E)) h)`. Take `⟨c, i, hi, hc⟩` from `w.isMaximal.exists_inv s.2`. Use `⟨a * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Establish `hc' : iota w c * iota w (s : 𝓞 E) + iota w i = 1`. Rewrite using `[← map_mul, ← map_add, hc, map_one]`. Establish `e1 : iota w (a * c) - x = -(x * iota w i)`. Rewrite using `[map_mul, ← hxs]`.

Take the linear combination `x * hc'`. Rewrite using `[e1]`. Conclude with `neg_mem (Ideal.mul_mem_left _ _ ((iota_mem_max w i).2 hi))`.
-/
private theorem res_surj :
    Function.Surjective ((IsLocalRing.residue (Gal.Int.Geo.Ow w)).comp (iota w)) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : E) ∈ w.valuationSubringAtPrime E := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact x.2
  haveI : IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj w.asIdeal.primeCompl
    (⟨x, hx⟩ : w.valuationSubringAtPrime E)
  have hxs : x * iota w (s : 𝓞 E) = iota w a :=
    Subtype.ext (congrArg (fun z : w.valuationSubringAtPrime E => (z : E)) h)
  obtain ⟨c, i, hi, hc⟩ := w.isMaximal.exists_inv s.2
  refine ⟨a * c, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hc' : iota w c * iota w (s : 𝓞 E) + iota w i = 1 := by
    rw [← map_mul, ← map_add, hc, map_one]
  have e1 : iota w (a * c) - x = -(x * iota w i) := by
    rw [map_mul, ← hxs]
    linear_combination x * hc'
  rw [e1]
  exact neg_mem (Ideal.mul_mem_left _ _ ((iota_mem_max w i).2 hi))

/- English proof (translation)
The claim follows from `(card_quot_of _ (res_surj w) w.asIdeal (fun a => by rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, iota_mem_max])).symm`.
-/
private theorem card_res :
    Nat.card (IsLocalRing.ResidueField (Gal.Int.Geo.Ow w)) = Nat.card (𝓞 E ⧸ w.asIdeal) :=
  (card_quot_of _ (res_surj w) w.asIdeal (fun a => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, iota_mem_max])).symm

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Qi54.card_pow <;> assumption`.
-/
private theorem card_pow (q : ℕ) (hq : q.Prime) (h : (q : 𝓞 E) ∈ w.asIdeal) :
    ∃ f : ℕ, Nat.card (𝓞 E ⧸ w.asIdeal) = q ^ f :=
  by apply _root_.UpperTheory.Reformulated.B.Qi54.card_pow <;> assumption

end Local

/- English proof (translation)
Introduce `q _ D ha hm E _ _ e gb hstd w 𝔴 r hpl hu N₀ h3 hcop`. Use `haveI : Subsingleton (Fin D.a) := by`. Rewrite using `[ha]`. Use `infer_instance`. Establish `hq : q.Prime` using `Fact.out`.

Set `j : 𝓞 D.F ≃+* 𝓞 E` to `NumberField.RingOfIntegers.mapRingEquiv e`. Establish `hj : ∀ c : 𝓞 D.F, ((j c : 𝓞 E) : E) = e (c : D.F)` using `fun c => rfl`. Establish `hpl' : ∀ c : 𝓞 D.F, c ∈ 𝔴 ↔ j c ∈ w.asIdeal` using `fun c => hpl c (j c) (hj c)`. Establish `hqm : (q : 𝓞 E) ∈ w.asIdeal`. Establish `h` using `(hpl' (q : 𝓞 D.F)).1 (hu (ES.p_mem_uIdeal D r))`.

Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨f, hf⟩` from `card_pow w q hq hqm`. Establish `hnw : Ideal.absNorm w.asIdeal = q ^ f`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, hf]`. Establish `hroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0`.

Take the linear combination `D.ω * D.tr_eq - D.nm_eq`. Set `t : 𝓞 D.F →+* Gal.Int.Geo.Ow w` to `(iota w).comp j.toRingHom`. Establish `hunit : ∀ k : ℕ, k.Coprime q → IsUnit (k : Gal.Int.Geo.Ow w)`. Introduce `k hk`. Establish `hkw : (k : 𝓞 E) ∉ w.asIdeal`.

Introduce `hmem`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hk`. Establish `h1 : (u : 𝓞 E) * (k : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) huv` after adjusting the coercions. Use `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)` and prove the remaining obligations.

Rewrite using `[← h1]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hqm)`. Assume the negation of the conclusion as `hn`. Use `hkw ((iota_mem_max w _).1 ?_)` and prove the remaining obligations. Rewrite using `[map_natCast]`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hn`. Set `b : Base D (Gal.Int.Geo.Ow w)` to `{ unit := hunit ρ := t D.ω ρ_root := by`. Establish `h` using `congrArg t hroot`. Simplify `h` using `only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero]`. Use `t := fun _ => t`.

Use `t_ω := fun _ => rfl`. Use `comax := fun i j h => absurd (Subsingleton.elim i j) h`. Use `apart := fun i j h => absurd (Subsingleton.elim i j) h }`. Use `⟨f, b, ⟨?_, ?_⟩, ?_, hqm, hnw⟩` and prove the remaining obligations. Conclude with `hstd.1`.

Conclude with `fun i => RingHom.ext fun c => hstd.2 i c`. Establish `hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp j.toRingHom)` using `Ideal.Quotient.mk_surjective.comp j.surjective`. Use `{ pmem := ?_ card := by rw [card_res, hf] three := h3 cop := hcop m1 := hm a1 := ha ule := hu norm := ?_ tw := fun i x hx => (iota_mem_max w _).2 ((hpl' x).1 hx) }` and prove the remaining obligations. Rewrite using `[← map_natCast (iota w)]`. Conclude with `(iota_mem_max w _).2 hqm`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, card_quot_of _ hsurj 𝔴 (fun a => by`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hpl' a), hf]`.
-/
theorem baseExtension_holds : Gal.Int.Geo.BaseEx := by
  intro q _ D ha hm E _ _ e gb hstd w 𝔴 r hpl hu N₀ h3 hcop
  haveI : Subsingleton (Fin D.a) := by
    rw [ha]
    infer_instance
  have hq : q.Prime := Fact.out
  let j : 𝓞 D.F ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hj : ∀ c : 𝓞 D.F, ((j c : 𝓞 E) : E) = e (c : D.F) := fun c => rfl
  have hpl' : ∀ c : 𝓞 D.F, c ∈ 𝔴 ↔ j c ∈ w.asIdeal := fun c => hpl c (j c) (hj c)
  have hqm : (q : 𝓞 E) ∈ w.asIdeal := by
    have h := (hpl' (q : 𝓞 D.F)).1 (hu (ES.p_mem_uIdeal D r))
    rwa [map_natCast] at h
  obtain ⟨f, hf⟩ := card_pow w q hq hqm
  have hnw : Ideal.absNorm w.asIdeal = q ^ f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hf]
  have hroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  let t : 𝓞 D.F →+* Gal.Int.Geo.Ow w := (iota w).comp j.toRingHom
  have hunit : ∀ k : ℕ, k.Coprime q → IsUnit (k : Gal.Int.Geo.Ow w) := by
    intro k hk
    have hkw : (k : 𝓞 E) ∉ w.asIdeal := by
      intro hmem
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
      have h1 : (u : 𝓞 E) * (k : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hqm)
    by_contra hn
    refine hkw ((iota_mem_max w _).1 ?_)
    rw [map_natCast]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let b : Base D (Gal.Int.Geo.Ow w) :=
    { unit := hunit
      ρ := t D.ω
      ρ_root := by
        have h := congrArg t hroot
        simpa only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] using h
      t := fun _ => t
      t_ω := fun _ => rfl
      comax := fun i j h => absurd (Subsingleton.elim i j) h
      apart := fun i j h => absurd (Subsingleton.elim i j) h }
  refine ⟨f, b, ⟨?_, ?_⟩, ?_, hqm, hnw⟩
  · exact hstd.1
  · exact fun i => RingHom.ext fun c => hstd.2 i c
  · have hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp j.toRingHom) :=
      Ideal.Quotient.mk_surjective.comp j.surjective
    refine
      { pmem := ?_
        card := by rw [card_res, hf]
        three := h3
        cop := hcop
        m1 := hm
        a1 := ha
        ule := hu
        norm := ?_
        tw := fun i x hx => (iota_mem_max w _).2 ((hpl' x).1 hx) }
    · rw [← map_natCast (iota w)]
      exact (iota_mem_max w _).2 hqm
    · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        card_quot_of _ hsurj 𝔴 (fun a => by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
          exact hpl' a), hf]

end UpperTheory
