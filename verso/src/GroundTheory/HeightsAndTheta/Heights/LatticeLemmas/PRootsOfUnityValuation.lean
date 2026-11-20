import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Finset

noncomputable section

namespace RootsOfUnityValuation

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨-1, by simp⟩`.
-/
theorem associated_sub_comm (a b : A) : Associated (a - b) (b - a) :=
  ⟨-1, by simp⟩

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, l = n + 1` from `⟨l - 1, (Nat.sub_add_cancel hl.one_lt.le).symm⟩`. Establish `h` using `hζ.prod_one_sub_pow_eq_order`. Establish `h1 : (1 - ζ) ^ n = ∏ _k ∈ range n, (1 - ζ)` using `by simp`. Rewrite using `[Nat.add_sub_cancel, h1]`. Use `push_cast`.

Rewrite using `[← h]`. Use `Associated.prod _ _ _ fun k hk => ?_` and prove the remaining obligations. Establish `hcop : (k + 1).Coprime (n + 1)` using `(Nat.coprime_of_lt_prime (by omega) (by simpa using Finset.mem_range.1 hk) hl).symm`. Conclude with `(associated_sub_comm 1 ζ).trans ((hζ.associated_sub_one_pow_sub_one_of_coprime hcop).trans (associated_sub_comm _ _))`.
-/
theorem one_sub_pow_associated {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) :
    Associated ((1 - ζ) ^ (l - 1)) (l : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_lt.le).symm⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h1 : (1 - ζ) ^ n = ∏ _k ∈ range n, (1 - ζ) := by simp
  rw [Nat.add_sub_cancel, h1]
  push_cast
  rw [← h]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hcop : (k + 1).Coprime (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by simpa using Finset.mem_range.1 hk) hl).symm
  exact (associated_sub_comm 1 ζ).trans
    ((hζ.associated_sub_one_pow_sub_one_of_coprime hcop).trans (associated_sub_comm _ _))

/- English proof (translation)
Establish `h` using `hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hl ((Polynomial.mem_nthRootsFinset hl.pos 1).2 hx) ((Polynomial.mem_nthRootsFinset hl.pos 1).2 hy) hxy`. Conclude with `((h.symm.trans (associated_sub_comm ζ 1)).pow_pow).trans (one_sub_pow_associated hl hζ)`.
-/
theorem sub_pow_associated {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) {x y : A}
    (hx : x ^ l = 1) (hy : y ^ l = 1) (hxy : x ≠ y) :
    Associated ((x - y) ^ (l - 1)) (l : A) := by
  have h := hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hl
    ((Polynomial.mem_nthRootsFinset hl.pos 1).2 hx) ((Polynomial.mem_nthRootsFinset hl.pos 1).2 hy)
    hxy
  exact ((h.symm.trans (associated_sub_comm ζ 1)).pow_pow).trans (one_sub_pow_associated hl hζ)

end RootsOfUnityValuation

/- English proof (translation)
Introduce `E _ _ l hl ζ hζ c c' hc hc' hne`. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Establish `hmem : ∀ x : 𝓞 E, x ^ l = 1 → x ∈ Algebra.adjoin ℤ {ζ}`. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hx`.

Conclude with `Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) i`. Set `z : Algebra.adjoin ℤ {ζ}` to `⟨ζ, Algebra.self_mem_adjoin_singleton ℤ ζ⟩`. Establish `hz : IsPrimitiveRoot z l` using `IsPrimitiveRoot.of_map_of_injective (f := (Algebra.adjoin ℤ {ζ}).val) hζ Subtype.val_injective`. Set `a : Algebra.adjoin ℤ {ζ}` to `⟨c, hmem c hc⟩`. Set `a' : Algebra.adjoin ℤ {ζ}` to `⟨c', hmem c' hc'⟩`.

Establish `ha : a ^ l = 1` using `Subtype.ext (by simpa [a] using hc)`. Establish `ha' : a' ^ l = 1` using `Subtype.ext (by simpa [a'] using hc')`. Establish `haa : a ≠ a'` using `fun h => hne (congrArg Subtype.val h)`. Use `⟨?_, ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hz.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hl ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha) ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha') haa`.

Use `⟨-u, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val hu`. Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, z, a, a'] at h`. Rewrite using `[← h, Units.val_neg, NegMemClass.coe_neg]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨w, hw⟩` from `RootsOfUnityValuation.one_sub_pow_associated hl hz`. Use `⟨w⁻¹, ?_⟩` and prove the remaining obligations. Establish `key : (1 - z) ^ (l - 1) = ((w⁻¹ : (Algebra.adjoin ℤ {ζ})ˣ) : Algebra.adjoin ℤ {ζ}) * l`. Rewrite using `[← hw, mul_comm, Units.mul_inv_cancel_right]`. Establish `h` using `congrArg Subtype.val key`.

Simplify `h` using `[z]`. Establish `hass` using `RootsOfUnityValuation.sub_pow_associated hl hζ hc hc' hne`. Establish `hv : ∀ x y : 𝓞 E, x ^ l = 1 → y ^ l = 1 → x ≠ y → x - y ∈ v.asIdeal → (l : 𝓞 E) ∈ v.asIdeal`. Introduce `x y hx hy hxy hm`. Take `⟨t, ht⟩` from `(RootsOfUnityValuation.sub_pow_associated hl hζ hx hy hxy).dvd`.

Rewrite using `[ht]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hm _ (by have := hl.two_le; omega))`. Establish `hcard : 0 < Nat.card (𝓞 E ⧸ v.asIdeal)`. Use `NumberField.HeightOneSpectrum.one_lt_absNorm v` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Use linear arithmetic over natural numbers and integers. Establish `: Finite (𝓞 E ⧸ v.asIdeal)` using `Nat.finite_of_card_ne_zero hcard.ne'`. Use `⟨fun hl' => ⟨?_, ?_, ?_⟩, fun hl' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, NumberField.HeightOneSpectrum.adicAbv, IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]`. Conclude with `fun hm => hl' (hv c c' hc hc' hne hm)`.

Introduce `x hx y hy hxy`. Assume the negation of the conclusion as `hne'`. Conclude with `hl' (hv x y hx hy hne' (Ideal.Quotient.eq.1 hxy))`. Establish `hunit : ∀ i : ℕ, Ideal.Quotient.mk v.asIdeal (ζ ^ i) ≠ 0`. Introduce `i h`.

Rewrite `h` using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((hζ.isUnit NeZero.out).pow i))`. Set `f : Option (Fin l) → 𝓞 E ⧸ v.asIdeal` to `fun o => o.elim 0 (fun i => Ideal.Quotient.mk v.asIdeal (ζ ^ (i : ℕ)))`. Establish `hroot : ∀ i : ℕ, (ζ ^ i) ^ l = 1` using `fun i => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`.

Establish `hinj : Function.Injective f`. Introduce and unpack `(_ | i) (_ | j) h`. Both sides reduce to the same expression. Conclude with `absurd h.symm (hunit j)`. Conclude with `absurd h (hunit i)`.

Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Apply `hζ.pow_inj i.2 j.2` to reduce the goal to its premises. Assume the negation of the conclusion as `hne'`. Conclude with `hl' (hv _ _ (hroot i) (hroot j) hne' (Ideal.Quotient.eq.1 h))`.

Use `Nat.card_le_card_of_injective f hinj` as an intermediate fact. Simplify `this` using `[Finite.card_option]`. Take `⟨w, hw⟩` from `hass`. Establish `hwE` using `congrArg (algebraMap (𝓞 E) E) hw`. Rewrite `hwE` using `[map_mul, map_pow, map_natCast]`.

Establish `hw1 : NumberField.HeightOneSpectrum.adicAbv E v (algebraMap (𝓞 E) E (w : 𝓞 E)) = 1`. Rewrite using `[NumberField.HeightOneSpectrum.adicAbv, IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]`. Conclude with `fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h w.isUnit)`. Rewrite using `[← hwE, map_mul, map_pow, hw1, mul_one]`. Establish `: Fact l.Prime` using `⟨hl⟩`.

Establish `h0 : ((l : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hl'`. Establish `: CharP (𝓞 E ⧸ v.asIdeal) l` using `(CharP.charP_iff_prime_eq_zero hl).2 h0`. Use `Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl l) (𝓞 E ⧸ v.asIdeal)).injective` as an intermediate fact.

Simplify `this` using `[Nat.card_zmod]`.
-/
theorem RootsOfUnityValuation.proof : RootsOfUnityValuation.Statement := by
  intro E _ _ l hl ζ hζ c c' hc hc' hne
  have : NeZero l := ⟨hl.ne_zero⟩
  have hmem : ∀ x : 𝓞 E, x ^ l = 1 → x ∈ Algebra.adjoin ℤ {ζ} := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) i
  let z : Algebra.adjoin ℤ {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton ℤ ζ⟩
  have hz : IsPrimitiveRoot z l :=
    IsPrimitiveRoot.of_map_of_injective (f := (Algebra.adjoin ℤ {ζ}).val) hζ Subtype.val_injective
  let a : Algebra.adjoin ℤ {ζ} := ⟨c, hmem c hc⟩
  let a' : Algebra.adjoin ℤ {ζ} := ⟨c', hmem c' hc'⟩
  have ha : a ^ l = 1 := Subtype.ext (by simpa [a] using hc)
  have ha' : a' ^ l = 1 := Subtype.ext (by simpa [a'] using hc')
  have haa : a ≠ a' := fun h => hne (congrArg Subtype.val h)
  refine ⟨?_, ?_, fun v => ?_⟩
  · obtain ⟨u, hu⟩ := hz.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hl
      ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha) ((Polynomial.mem_nthRootsFinset hl.pos 1).2 ha')
      haa
    refine ⟨-u, ?_⟩
    have h := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, z, a, a'] at h
    rw [← h, Units.val_neg, NegMemClass.coe_neg]
    ring
  · obtain ⟨w, hw⟩ := RootsOfUnityValuation.one_sub_pow_associated hl hz
    refine ⟨w⁻¹, ?_⟩
    have key : (1 - z) ^ (l - 1) = ((w⁻¹ : (Algebra.adjoin ℤ {ζ})ˣ) : Algebra.adjoin ℤ {ζ}) * l := by
      rw [← hw, mul_comm, Units.mul_inv_cancel_right]
    have h := congrArg Subtype.val key
    simpa [z] using h
  · have hass := RootsOfUnityValuation.sub_pow_associated hl hζ hc hc' hne
    have hv : ∀ x y : 𝓞 E, x ^ l = 1 → y ^ l = 1 → x ≠ y → x - y ∈ v.asIdeal →
        (l : 𝓞 E) ∈ v.asIdeal := by
      intro x y hx hy hxy hm
      obtain ⟨t, ht⟩ := (RootsOfUnityValuation.sub_pow_associated hl hζ hx hy hxy).dvd
      rw [ht]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hm _ (by have := hl.two_le; omega))
    have hcard : 0 < Nat.card (𝓞 E ⧸ v.asIdeal) := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
      omega
    have : Finite (𝓞 E ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero hcard.ne'
    refine ⟨fun hl' => ⟨?_, ?_, ?_⟩, fun hl' => ⟨?_, ?_⟩⟩
    · rw [RingOfIntegers.coe_eq_algebraMap, NumberField.HeightOneSpectrum.adicAbv,
        IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]
      exact fun hm => hl' (hv c c' hc hc' hne hm)
    · intro x hx y hy hxy
      by_contra hne'
      exact hl' (hv x y hx hy hne' (Ideal.Quotient.eq.1 hxy))
    · have hunit : ∀ i : ℕ, Ideal.Quotient.mk v.asIdeal (ζ ^ i) ≠ 0 := by
        intro i h
        rw [Ideal.Quotient.eq_zero_iff_mem] at h
        exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((hζ.isUnit NeZero.out).pow i))
      let f : Option (Fin l) → 𝓞 E ⧸ v.asIdeal :=
        fun o => o.elim 0 (fun i => Ideal.Quotient.mk v.asIdeal (ζ ^ (i : ℕ)))
      have hroot : ∀ i : ℕ, (ζ ^ i) ^ l = 1 := fun i => by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      have hinj : Function.Injective f := by
        rintro (_ | i) (_ | j) h
        · rfl
        · exact absurd h.symm (hunit j)
        · exact absurd h (hunit i)
        · congr 1
          apply Fin.ext
          apply hζ.pow_inj i.2 j.2
          by_contra hne'
          exact hl' (hv _ _ (hroot i) (hroot j) hne' (Ideal.Quotient.eq.1 h))
      have := Nat.card_le_card_of_injective f hinj
      simpa [Finite.card_option] using this
    · obtain ⟨w, hw⟩ := hass
      have hwE := congrArg (algebraMap (𝓞 E) E) hw
      rw [map_mul, map_pow, map_natCast] at hwE
      have hw1 : NumberField.HeightOneSpectrum.adicAbv E v (algebraMap (𝓞 E) E (w : 𝓞 E)) = 1 := by
        rw [NumberField.HeightOneSpectrum.adicAbv,
          IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]
        exact fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h w.isUnit)
      rw [← hwE, map_mul, map_pow, hw1, mul_one]
    · have : Fact l.Prime := ⟨hl⟩
      have h0 : ((l : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact hl'
      have : CharP (𝓞 E ⧸ v.asIdeal) l := (CharP.charP_iff_prime_eq_zero hl).2 h0
      have := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl l) (𝓞 E ⧸ v.asIdeal)).injective
      simpa [Nat.card_zmod] using this

end

end GroundTheory.Heights₂.Heights
