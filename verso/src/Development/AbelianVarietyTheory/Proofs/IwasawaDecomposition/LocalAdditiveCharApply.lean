import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues

open NumberField IsDedekindDomain Formalism.L2.Col
open Formalism.L2.Host (HChar atFin IsUnitAt)

noncomputable section

namespace GlobalTheory.TrueChars

def liftHom {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Monoid G] (f : G →* ℂ) (h : ∀ g, ∃ y, σ y = f g) : G →* K where
  toFun g := (h g).choose
  map_one' := σ.injective (by rw [(h 1).choose_spec, map_one, map_one])
  map_mul' a b := σ.injective (by
    rw [map_mul σ, (h (a * b)).choose_spec, (h a).choose_spec, (h b).choose_spec, map_mul])

/- English proof (translation)
The claim follows from `(h g).choose_spec`.
-/
theorem liftHom_spec {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Monoid G] (f : G →* ℂ) (h : ∀ g, ∃ y, σ y = f g)
    (g : G) : σ (liftHom σ f h g) = f g := (h g).choose_spec

open Classical in

def pullUnit {K : Type} [Field K] (σ : K →+* ℂ) (z : ℂ) : Kˣ := if h : ∃ y : Kˣ, σ y = z then h.choose else 1

/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Conclude with `hz (by rw [← hy, map_zero])`. Establish `h' : ∃ y : Kˣ, σ y = z` using `⟨Units.mk0 y hy0, hy⟩`.

Unfold `pullUnit`. Rewrite using `[dif_pos h']`. Conclude with `h'.choose_spec`.
-/
theorem pullUnit_spec {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (hz : z ≠ 0) (h : ∃ y, σ y = z) :
    σ (pullUnit σ z : K) = z := by
  obtain ⟨y, hy⟩ := h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hz (by rw [← hy, map_zero])
  have h' : ∃ y : Kˣ, σ y = z := ⟨Units.mk0 y hy0, hy⟩
  unfold pullUnit
  rw [dif_pos h']
  exact h'.choose_spec

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Take `⟨i, -, hi⟩` from `(hy.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz`. Conclude with `⟨y ^ i, by rw [map_pow, hi]⟩`.
-/
theorem roots_of_isPrimitiveRoot {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (hn : n ≠ 0) {y : K}
    (hy : IsPrimitiveRoot y n) (z : ℂ) (hz : z ^ n = 1) : ∃ x, σ x = z := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨i, -, hi⟩ := (hy.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  exact ⟨y ^ i, by rw [map_pow, hi]⟩

section ZMod

variable {K : Type} [Field K] (σ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
  (hr : ∀ z : ℂ, z ^ (p * (p - 1)) = 1 → ∃ y, σ y = z)

def omK (om : (ZMod p)ˣ →* ℂˣ) : (ZMod p)ˣ →* Kˣ :=
  (liftHom σ ((Units.coeHom ℂ).comp om) fun a => hr _ (by
    haveI := Fact.mk hp
    have h1 : a ^ (p - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one p a
    rw [← map_pow, mul_comm, pow_mul, h1, one_pow, map_one])).toHomUnits

/- English proof (translation)
The claim follows from `liftHom_spec σ _ _ a`.
-/
theorem omK_spec (om : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ) : σ (omK σ hp hr om a : K) = (om a : ℂ) :=
  liftHom_spec σ _ _ a

/- English proof (translation)
Introduce `a b h`. Apply `hom` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← omK_spec σ hp hr, ← omK_spec σ hp hr, h]`.
-/
theorem omK_injective {om : (ZMod p)ˣ →* ℂˣ} (hom : Function.Injective om) : Function.Injective (omK σ hp hr om) := by
  intro a b h
  apply hom
  apply Units.ext
  rw [← omK_spec σ hp hr, ← omK_spec σ hp hr, h]

def psiK : AddChar (ZMod p) K :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  AddChar.toMonoidHomEquiv.symm (liftHom σ (ZMod.stdAddChar (N := p)).toMonoidHom fun a => hr _ (by
    have h1 : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [← map_pow, pow_mul, h1, one_pow, map_one]))

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Rewrite using `[← ZMod.stdAddChar_coe]`. Conclude with `liftHom_spec σ _ _ (Multiplicative.ofAdd (b : ZMod p))`.
-/
theorem psiK_spec (b : ℤ) :
    σ (psiK σ hp hr (b : ZMod p)) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.stdAddChar_coe]
  exact liftHom_spec σ _ _ (Multiplicative.ofAdd (b : ZMod p))

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Use `haveI := Fact.mk hp`. Introduce `h`. Establish `h1 : σ (psiK σ hp hr 1) = ZMod.stdAddChar (1 : ZMod p)` using `liftHom_spec σ _ _ (Multiplicative.ofAdd (1 : ZMod p))`. Rewrite `h1` using `[h, map_one, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p))]`.

Conclude with `zero_ne_one (ZMod.injective_stdAddChar h1)`.
-/
theorem psiK_one : psiK σ hp hr 1 ≠ 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := Fact.mk hp
  intro h
  have h1 : σ (psiK σ hp hr 1) = ZMod.stdAddChar (1 : ZMod p) :=
    liftHom_spec σ _ _ (Multiplicative.ofAdd (1 : ZMod p))
  rw [h, map_one, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p))] at h1
  exact zero_ne_one (ZMod.injective_stdAddChar h1)

end ZMod

/- English proof (translation)
Establish `hv' : w.valuation L (y' : L) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hy`. Establish `hlt : w.valuation L ((y - y' : 𝓞 L) : L) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hyy`. Establish `hy0 : (y' : L) ≠ 0` using `hx' ▸ x'.ne_zero`. Establish `e : ((x * x'⁻¹ : Lˣ) : L) - 1 = ((y - y' : 𝓞 L) : L) * (y' : L)⁻¹`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, hx, hx']`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `h1 : w.valuation L (((x * x'⁻¹ : Lˣ) : L) - 1) < 1`. Rewrite using `[e, map_mul, map_inv₀, hv', inv_one, mul_one]`. Conclude with `hlt`.

Establish `h2 : Valued.v (((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) < 1`. Establish `h3 : ((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 = algebraMap L (w.adicCompletion L) (((x * x'⁻¹ : Lˣ) : L) - 1)`. Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Rewrite using `[h3, ReciprocityTheory.Aut.adic_valued_algebraMap]`.

Conclude with `h1`. Establish `h4 : IsUnitAt w (atFin w (x * x'⁻¹))`. Use `Valuation.map_eq_of_sub_lt Valued.v (x := (1 : w.adicCompletion L)) (y := ((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L)) (by rwa [map_one])` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `h5 : χ.locK w (x * x'⁻¹) = 1`.

Use `ht _ h4 ?_` and prove the remaining obligations. Generalize the expression as in `Valued.v (((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) = g at h2`. Distinguish the cases in `hg : g = 0`. Rewrite using `[hg]`. Conclude with `zero_le`.

Rewrite `h2`, the goal using `[← WithZero.exp_log hg]`. Rewrite `h2` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Rewrite `h5` using `[map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem locK_congr {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) (ht : χ.TameAt w)
    (x x' : Lˣ) (y y' : 𝓞 L) (hx : (x : L) = y) (hx' : (x' : L) = y') (hy : y' ∉ w.asIdeal)
    (hyy : y - y' ∈ w.asIdeal) : χ.locK w x = χ.locK w x' := by
  have hv' : w.valuation L (y' : L) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hy
  have hlt : w.valuation L ((y - y' : 𝓞 L) : L) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hyy
  have hy0 : (y' : L) ≠ 0 := hx' ▸ x'.ne_zero
  have e : ((x * x'⁻¹ : Lˣ) : L) - 1 = ((y - y' : 𝓞 L) : L) * (y' : L)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hx, hx']
    push_cast
    field_simp
  have h1 : w.valuation L (((x * x'⁻¹ : Lˣ) : L) - 1) < 1 := by
    rw [e, map_mul, map_inv₀, hv', inv_one, mul_one]
    exact hlt
  have h2 : Valued.v (((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) < 1 := by
    have h3 : ((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1
        = algebraMap L (w.adicCompletion L) (((x * x'⁻¹ : Lˣ) : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    rw [h3, ReciprocityTheory.Aut.adic_valued_algebraMap]
    exact h1
  have h4 : IsUnitAt w (atFin w (x * x'⁻¹)) := by
    have := Valuation.map_eq_of_sub_lt Valued.v (x := (1 : w.adicCompletion L))
      (y := ((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L)) (by rwa [map_one])
    rwa [map_one] at this
  have h5 : χ.locK w (x * x'⁻¹) = 1 := by
    refine ht _ h4 ?_
    generalize Valued.v (((atFin w (x * x'⁻¹) : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) = g at h2
    by_cases hg : g = 0
    · rw [hg]; exact zero_le
    · rw [← WithZero.exp_log hg] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
  rwa [map_mul, map_inv, mul_inv_eq_one] at h5

/- English proof (translation)
Establish `hprod : Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm (Ideal.span {a}) = p ^ 2`. Rewrite using `[← map_mul, Ideal.span_singleton_mul_span_singleton, mul_comm, hab, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]`. Take `⟨i, hi, he⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro _ hprod)`. Use `interval_cases i`. Rewrite `he` using `[pow_zero, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]`.

Conclude with `absurd he hb`. Rewrite using `[he, pow_one]`. Rewrite `hprod` using `[he]`. Establish `h1 : Ideal.absNorm (Ideal.span {a}) = 1` using `Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [hprod, mul_one])`. Rewrite `h1` using `[Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]`.

Conclude with `absurd h1 ha`.
-/
theorem absNorm_span_of_mul_eq {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {a b : 𝓞 K} (hab : a * b = p) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : Ideal.absNorm (Ideal.span {b}) = p := by
  have hprod : Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm (Ideal.span {a}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, mul_comm, hab, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank, h2]
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hprod)
  interval_cases i
  · rw [pow_zero, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at he
    exact absurd he hb
  · rw [he, pow_one]
  · rw [he] at hprod
    have h1 : Ideal.absNorm (Ideal.span {a}) = 1 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [hprod, mul_one])
    rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
    exact absurd h1 ha

/- English proof (translation)
Establish `hprime : (Ideal.span {b}).IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hb]; exact hp)`. Establish `hb0 : Ideal.span {b} ≠ ⊥`. Introduce `h`. Rewrite `hb` using `[h, Ideal.absNorm_bot]`. Conclude with `hp.ne_zero hb.symm`.

Set `P : HeightOneSpectrum (𝓞 K)` to `⟨Ideal.span {b}, hprime, hb0⟩`. Use `set J := RingOfIntegers.mapRingHom j with hJ`. Establish `hle : ∀ w : HeightOneSpectrum (𝓞 E), J b ∈ w.asIdeal → P.asIdeal = w.asIdeal.comap J` using `fun w hw => P.isMaximal.eq_of_le (Ideal.comap_ne_top J w.isPrime.ne_top) ((Ideal.span_singleton_le_iff_mem _).2 hw)`. Establish `hcong : ∀ (y : 𝓞 K) (a : ℕ), y - (a : 𝓞 K) ∈ P.asIdeal → ∀ w : HeightOneSpectrum (𝓞 E), J b ∈ w.asIdeal → Ideal.Quotient.mk w.asIdeal (J y) = a` using `fun y a h w hw => by`. Rewrite `h` using `[hle w hw, Ideal.mem_comap, map_sub, map_natCast, ← Ideal.Quotient.eq, map_natCast]`.

Conclude with `h`. Establish `hmul : ∀ (r s : 𝓞 K), x * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r → ∀ w : HeightOneSpectrum (𝓞 E), IntAt w (j x) → Ideal.Quotient.mk w.asIdeal (J s) * redP w (j x) = Ideal.Quotient.mk w.asIdeal (J r)` using `fun r s h w hw => by`. Rewrite using `[← reduction_coe, ← reduction_coe, ← reduction_mul (IntAt.coe _ _) hw]`. Use `congr 1`. Use `congrArg j h` as an intermediate fact.

Rewrite `this` using `[map_mul, mul_comm]`. Conclude with `this`. Take `⟨n, ⟨d, hd⟩, h⟩` from `P.exists_primeCompl_mul_eq_or_mul_eq (K := K) x`. Take `⟨n', hn'⟩` from `exists_nat_congr_of_absNorm_prime P.asIdeal hprime.ne_top hp hb n`. Take `⟨d', hd'⟩` from `exists_nat_congr_of_absNorm_prime P.asIdeal hprime.ne_top hp hb d`.

Use `⟨n', d', fun w hw => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcong d d' hd' w hw]`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Use `show d ∈ P.asIdeal`.

Rewrite using `[hle w hw, Ideal.mem_comap]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h0`. Break down `h with h | h` into its components or cases. Use `left`. Introduce `w hw hi`.

Rewrite using `[← hcong d d' hd' w hw, ← hcong n n' hn' w hw]`. Conclude with `hmul n d h w hi`. Use `right`. Introduce `w hw hi`. Rewrite using `[← hcong d d' hd' w hw, ← hcong n n' hn' w hw]`.

Conclude with `hmul d n h w hi`.
-/
theorem exists_nat_red {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] (j : K →+* E) {p : ℕ}
    (hp : p.Prime) {b : 𝓞 K} (hb : Ideal.absNorm (Ideal.span {b}) = p) (x : K) :
    ∃ n d : ℕ, (∀ w : HeightOneSpectrum (𝓞 E), RingOfIntegers.mapRingHom j b ∈ w.asIdeal →
        (d : 𝓞 E ⧸ w.asIdeal) ≠ 0) ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), RingOfIntegers.mapRingHom j b ∈ w.asIdeal → IntAt w (j x) →
        (d : 𝓞 E ⧸ w.asIdeal) * redP w (j x) = n) ∨
      (∀ w : HeightOneSpectrum (𝓞 E), RingOfIntegers.mapRingHom j b ∈ w.asIdeal → IntAt w (j x) →
        (n : 𝓞 E ⧸ w.asIdeal) * redP w (j x) = d)) := by
  have hprime : (Ideal.span {b}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hb]; exact hp)
  have hb0 : Ideal.span {b} ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hb
    exact hp.ne_zero hb.symm
  let P : HeightOneSpectrum (𝓞 K) := ⟨Ideal.span {b}, hprime, hb0⟩
  set J := RingOfIntegers.mapRingHom j with hJ
  have hle : ∀ w : HeightOneSpectrum (𝓞 E), J b ∈ w.asIdeal → P.asIdeal = w.asIdeal.comap J := fun w hw =>
    P.isMaximal.eq_of_le (Ideal.comap_ne_top J w.isPrime.ne_top) ((Ideal.span_singleton_le_iff_mem _).2 hw)
  have hcong : ∀ (y : 𝓞 K) (a : ℕ), y - (a : 𝓞 K) ∈ P.asIdeal → ∀ w : HeightOneSpectrum (𝓞 E), J b ∈ w.asIdeal →
      Ideal.Quotient.mk w.asIdeal (J y) = a := fun y a h w hw => by
    rw [hle w hw, Ideal.mem_comap, map_sub, map_natCast, ← Ideal.Quotient.eq, map_natCast] at h
    exact h
  have hmul : ∀ (r s : 𝓞 K), x * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r → ∀ w : HeightOneSpectrum (𝓞 E),
      IntAt w (j x) → Ideal.Quotient.mk w.asIdeal (J s) * redP w (j x) = Ideal.Quotient.mk w.asIdeal (J r) :=
    fun r s h w hw => by
    rw [← reduction_coe, ← reduction_coe, ← reduction_mul (IntAt.coe _ _) hw]
    congr 1
    have := congrArg j h
    rw [map_mul, mul_comm] at this
    exact this
  obtain ⟨n, ⟨d, hd⟩, h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  obtain ⟨n', hn'⟩ := exists_nat_congr_of_absNorm_prime P.asIdeal hprime.ne_top hp hb n
  obtain ⟨d', hd'⟩ := exists_nat_congr_of_absNorm_prime P.asIdeal hprime.ne_top hp hb d
  refine ⟨n', d', fun w hw => ?_, ?_⟩
  · rw [← hcong d d' hd' w hw]
    intro h0
    apply hd
    show d ∈ P.asIdeal
    rw [hle w hw, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  · rcases h with h | h
    · left
      intro w hw hi
      rw [← hcong d d' hd' w hw, ← hcong n n' hn' w hw]
      exact hmul n d h w hi
    · right
      intro w hw hi
      rw [← hcong d d' hd' w hw, ← hcong n n' hn' w hw]
      exact hmul d n h w hi

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Use `(mem_divs ?_ w).1 hw` and prove the remaining obligations. Introduce `h`. Establish `h1` using `hPr.piG_norm i`. Rewrite `h1` using `[h, mul_zero]`. Conclude with `(hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)`.
-/
theorem conj_mem (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    X.conjO (Pr.piG i) ∈ w.asIdeal := by
  refine (mem_divs ?_ w).1 hw
  intro h
  have h1 := hPr.piG_norm i
  rw [h, mul_zero] at h1
  exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)

/- English proof (translation)
Establish `hp` using `hPr.g_prime i`. Use `Fact.mk hp` as an intermediate fact. Establish `hbar : ((X.conjO (Pr.piG i) : 𝓞 X.E) : X.E) ∈ X.Kq`. Introduce `τ τ'`. Use `show X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) = X.emb τ' (star ((Pr.piG i : 𝓞 X.E) : X.E))`.

Rewrite using `[hX.emb_star, hX.emb_star, hPr.piG_Kq i τ τ']`. Establish `hint : ∀ (y : 𝓞 X.E) (hy : (y : X.E) ∈ X.Kq), ∃ a : 𝓞 X.Kq, RingOfIntegers.mapRingHom X.Kq.subtype a = y` using `fun y hy => by`. Establish `h1 : IsIntegral ℤ (⟨y, hy⟩ : X.Kq)` using `(isIntegral_algHom_iff X.Kq.subtype.toIntAlgHom X.Kq.subtype.injective).1 y.isIntegral_coe`. Conclude with `⟨⟨⟨y, hy⟩, h1⟩, rfl⟩`. Take `⟨a, ha⟩` from `hint _ (hPr.piG_Kq i)`.

Take `⟨b, hb⟩` from `hint _ hbar`. Establish `hinj : Function.Injective (RingOfIntegers.mapRingHom X.Kq.subtype)` using `fun u v h => RingOfIntegers.ext (X.Kq.subtype.injective (congrArg (fun z : 𝓞 X.E => (z : X.E)) h))`. Establish `hab : a * b = (Pr.g i : 𝓞 X.Kq)` using `hinj (by rw [map_mul, ha, hb, map_natCast, hPr.piG_norm])`. Establish `hnu : ¬ IsUnit (X.conjO (Pr.piG i))` using `fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (conj_mem hPr hw) h)`. Establish `hN` using `absNorm_span_of_mul_eq hX.quad hp hab (fun h => hnu (ha ▸ (h.map (RingOfIntegers.mapRingHom X.Kq.subtype)).map X.conjO)) (fun h => hnu (hb ▸ h.map (RingOfIntegers.mapRingHom X.Kq.subtype)))`.

Take `⟨n, d, hd, h⟩` from `exists_nat_red X.Kq.subtype hp hN ⟨x, hx⟩`. Rewrite `hd`, `h` using `[hb]`. Establish `hd0 : (d : ZMod (Pr.g i)) ≠ 0`. Rewrite using `[← map_natCast φ]`. Conclude with `fun h0 => hd w (conj_mem hPr hw) (φ.injective (by rw [h0, map_zero]))`.

Break down `h with h | h` into its components or cases. Establish `h1` using `congrArg φ (h w (conj_mem hPr hw) hi)`. Establish `h2` using `congrArg φ' (h w' (conj_mem hPr hw') hi')`. Rewrite `h1`, `h2` using `[map_mul, map_natCast, map_natCast]`. Conclude with `mul_left_cancel₀ hd0 (h1.trans h2.symm)`.

Establish `h1` using `congrArg φ (h w (conj_mem hPr hw) hi)`. Establish `h2` using `congrArg φ' (h w' (conj_mem hPr hw') hi')`. Rewrite `h1`, `h2` using `[map_mul, map_natCast, map_natCast]`. Establish `hn0 : (n : ZMod (Pr.g i)) ≠ 0` using `fun h0 => hd0 (by rw [← h1, h0, zero_mul])`. Conclude with `mul_left_cancel₀ hn0 (h1.trans h2.symm)`.
-/
theorem red_same (hX : X.Ok) (hPr : Pr.Ok) {i : Fin 2} {w w' : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i)
    (hw' : w' ∈ Pr.vG i) (φ : (𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod (Pr.g i)) (φ' : (𝓞 X.E ⧸ w'.asIdeal) ≃+* ZMod (Pr.g i))
    {x : X.E} (hx : x ∈ X.Kq) (hi : IntAt w x) (hi' : IntAt w' x) : φ (redP w x) = φ' (redP w' x) := by
  have hp := hPr.g_prime i
  have := Fact.mk hp
  have hbar : ((X.conjO (Pr.piG i) : 𝓞 X.E) : X.E) ∈ X.Kq := by
    intro τ τ'
    show X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) = X.emb τ' (star ((Pr.piG i : 𝓞 X.E) : X.E))
    rw [hX.emb_star, hX.emb_star, hPr.piG_Kq i τ τ']
  have hint : ∀ (y : 𝓞 X.E) (hy : (y : X.E) ∈ X.Kq), ∃ a : 𝓞 X.Kq, RingOfIntegers.mapRingHom X.Kq.subtype a = y :=
    fun y hy => by
    have h1 : IsIntegral ℤ (⟨y, hy⟩ : X.Kq) :=
      (isIntegral_algHom_iff X.Kq.subtype.toIntAlgHom X.Kq.subtype.injective).1 y.isIntegral_coe
    exact ⟨⟨⟨y, hy⟩, h1⟩, rfl⟩
  obtain ⟨a, ha⟩ := hint _ (hPr.piG_Kq i)
  obtain ⟨b, hb⟩ := hint _ hbar
  have hinj : Function.Injective (RingOfIntegers.mapRingHom X.Kq.subtype) := fun u v h =>
    RingOfIntegers.ext (X.Kq.subtype.injective (congrArg (fun z : 𝓞 X.E => (z : X.E)) h))
  have hab : a * b = (Pr.g i : 𝓞 X.Kq) := hinj (by rw [map_mul, ha, hb, map_natCast, hPr.piG_norm])
  have hnu : ¬ IsUnit (X.conjO (Pr.piG i)) := fun h =>
    w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (conj_mem hPr hw) h)
  have hN := absNorm_span_of_mul_eq hX.quad hp hab
    (fun h => hnu (ha ▸ (h.map (RingOfIntegers.mapRingHom X.Kq.subtype)).map X.conjO))
    (fun h => hnu (hb ▸ h.map (RingOfIntegers.mapRingHom X.Kq.subtype)))
  obtain ⟨n, d, hd, h⟩ := exists_nat_red X.Kq.subtype hp hN ⟨x, hx⟩
  rw [hb] at hd h
  have hd0 : (d : ZMod (Pr.g i)) ≠ 0 := by
    rw [← map_natCast φ]
    exact fun h0 => hd w (conj_mem hPr hw) (φ.injective (by rw [h0, map_zero]))
  rcases h with h | h
  · have h1 := congrArg φ (h w (conj_mem hPr hw) hi)
    have h2 := congrArg φ' (h w' (conj_mem hPr hw') hi')
    rw [map_mul, map_natCast, map_natCast] at h1 h2
    exact mul_left_cancel₀ hd0 (h1.trans h2.symm)
  · have h1 := congrArg φ (h w (conj_mem hPr hw) hi)
    have h2 := congrArg φ' (h w' (conj_mem hPr hw') hi')
    rw [map_mul, map_natCast, map_natCast] at h1 h2
    have hn0 : (n : ZMod (Pr.g i)) ≠ 0 := fun h0 => hd0 (by rw [← h1, h0, zero_mul])
    exact mul_left_cancel₀ hn0 (h1.trans h2.symm)

/- English proof (translation)
Take `⟨n, ⟨d, hd⟩, h⟩` from `w.exists_primeCompl_mul_eq_of_integer x hx.le`. Establish `hd' : d ∉ w.asIdeal` using `hd`. Establish `h' : algebraMap (𝓞 E) E d * x = algebraMap (𝓞 E) E n` using `by rw [mul_comm]; exact h`. Use `⟨⟨n, d, hd', h'⟩, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h1` using `reduction_spec w hd' h'`.

Rewrite `h1` using `[h0, mul_zero]`. Establish `h2 : w.valuation E (algebraMap (𝓞 E) E n) = 1`. Rewrite using `[← h', map_mul, hx, (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hd', one_mul]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem w).1 h2 (Ideal.Quotient.eq_zero_iff_mem.1 h1.symm)`.
-/
theorem unit_of_valuation {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {x : E}
    (hx : w.valuation E x = 1) : IntAt w x ∧ redP w x ≠ 0 := by
  obtain ⟨n, ⟨d, hd⟩, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx.le
  have hd' : d ∉ w.asIdeal := hd
  have h' : algebraMap (𝓞 E) E d * x = algebraMap (𝓞 E) E n := by rw [mul_comm]; exact h
  refine ⟨⟨n, d, hd', h'⟩, fun h0 => ?_⟩
  have h1 := reduction_spec w hd' h'
  rw [h0, mul_zero] at h1
  have h2 : w.valuation E (algebraMap (𝓞 E) E n) = 1 := by
    rw [← h', map_mul, hx, (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hd', one_mul]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).1 h2 (Ideal.Quotient.eq_zero_iff_mem.1 h1.symm)

open Classical in

def idx (w : {w // w ∈ Pr.vGs}) : Fin 2 := if w.1 ∈ Pr.vG 0 then 0 else 1

/- English proof (translation)
Unfold `idx`. Use `split_ifs with h`. Conclude with `h`. Establish `h2` using `w.2`. Unfold `Primes.vGs at h2`.

Conclude with `(Finset.mem_union.1 h2).resolve_left h`.
-/
theorem idx_mem (w : {w // w ∈ Pr.vGs}) : w.1 ∈ Pr.vG (idx w) := by
  classical
  unfold idx
  split_ifs with h
  · exact h
  · have h2 := w.2
    unfold Primes.vGs at h2
    exact (Finset.mem_union.1 h2).resolve_left h

/- English proof (translation)
Establish `hg : Function.Injective Pr.g`. Introduce `i j hij`. Use `hPr.g_ne` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`. Conclude with `hg ((hPr.vG_norm _ w.1 (idx_mem w)).symm.trans (hPr.vG_norm i w.1 hi))`.
-/
theorem idx_eq (hPr : Pr.Ok) (w : {w // w ∈ Pr.vGs}) {i : Fin 2} (hi : w.1 ∈ Pr.vG i) : idx w = i := by
  have hg : Function.Injective Pr.g := by
    intro i j hij
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all
  exact hg ((hPr.vG_norm _ w.1 (idx_mem w)).symm.trans (hPr.vG_norm i w.1 hi))

def resEquiv (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hi : w ∈ Pr.vG i) :
    (𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod (Pr.g i) :=
  Classical.choice (GlobalTheory.BaseChars.nonempty_equiv_zmod (hPr.g_prime i) w (hPr.vG_norm i w hi))

def trueChars (hPr : Pr.Ok) {m : ℕ} (σ₀ : X.K →+* ℂ)
    (hr : ∀ (i : Fin 2) (z : ℂ), z ^ (Pr.g i * (Pr.g i - 1)) = 1 → ∃ y, σ₀ y = z)
    (om : ∀ i : Fin 2, (ZMod (Pr.g i))ˣ →* ℂˣ) (mu : Fin m → HChar X.E) (eta : HChar X.E) (xi0 : X.E) :
    Chars X Pr m where
  psi0 w := ((psiK σ₀ (hPr.g_prime (idx w)) (hr (idx w))).compAddMonoidHom
    (resEquiv hPr (idx_mem w)).toAddMonoidHom).mulShift (redP w.1 xi0)
  chi j w := ((omK σ₀ (hPr.g_prime (idx w)) (hr (idx w)) (om (idx w))).comp
    (Units.map (resEquiv hPr (idx_mem w)).toMonoidHom)) ^ (2 * (j.1 + 1))
  muVal j v := pullUnit σ₀ ((mu j).valTw 0 v)
  etaVal v := pullUnit σ₀ (eta.valTw (1 / 2) v)

section Props

variable (hPr : Pr.Ok) {m : ℕ} (σ₀ : X.K →+* ℂ)
  (hr : ∀ (i : Fin 2) (z : ℂ), z ^ (Pr.g i * (Pr.g i - 1)) = 1 → ∃ y, σ₀ y = z)
  (om : ∀ i : Fin 2, (ZMod (Pr.g i))ˣ →* ℂˣ) (mu : Fin m → HChar X.E) (eta : HChar X.E) (xi0 : X.E)

/- English proof (translation)
Take `rfl` from `idx_eq hPr w hi`. Both sides reduce to the same expression.
-/
theorem local_additive_char_apply (w : {w // w ∈ Pr.vGs}) {i : Fin 2} (hi : w.1 ∈ Pr.vG i) (c : 𝓞 X.E ⧸ w.1.asIdeal) :
    (trueChars hPr σ₀ hr om mu eta xi0).psi0 w c
      = psiK σ₀ (hPr.g_prime i) (hr i) (resEquiv hPr hi (redP w.1 xi0 * c)) := by
  obtain rfl := idx_eq hPr w hi
  rfl

/- English proof (translation)
Take `rfl` from `idx_eq hPr w hi`. Take `rfl : Units.map (resEquiv hPr hi).toMonoidHom c = a` from `Units.ext h`. Both sides reduce to the same expression.
-/
theorem chi_apply (w : {w // w ∈ Pr.vGs}) {i : Fin 2} (hi : w.1 ∈ Pr.vG i) (j : Fin m)
    (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (a : (ZMod (Pr.g i))ˣ) (h : resEquiv hPr hi c = a) :
    (trueChars hPr σ₀ hr om mu eta xi0).chi j w c = omK σ₀ (hPr.g_prime i) (hr i) (om i) a ^ (2 * (j.1 + 1)) := by
  obtain rfl := idx_eq hPr w hi
  obtain rfl : Units.map (resEquiv hPr hi).toMonoidHom c = a := Units.ext h
  rfl

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w h`. Establish `hi` using `idx_mem w`. Use `Fact.mk (hPr.g_prime (idx w))` as an intermediate fact. Establish `h0 : resEquiv hPr hi (redP w.1 xi0) ≠ 0` using `fun h0 => (hxi w).2 ((resEquiv hPr hi).injective (by rw [h0, map_zero]))`.

Establish `h1` using `local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi ((resEquiv hPr hi).symm (resEquiv hPr hi (redP w.1 xi0))⁻¹)`. Rewrite `h1` using `[h, map_mul, RingEquiv.apply_symm_apply, mul_inv_cancel₀ h0]`. Conclude with `psiK_one σ₀ _ _ h1.symm`. Introduce `w j j' h`. Establish `hi` using `idx_mem w`.

Establish `hj` using `j.2`. Establish `hj'` using `j'.2`. Establish `hmi` using `hm (idx w)`. Establish `h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1)`. Use `GlobalTheory.BaseChars.eq_of_pow_eq (hPr.g_prime _) (omK_injective σ₀ (hPr.g_prime _) (hr _) (hom (idx w))) (by omega) (by omega) fun a => ?_` and prove the remaining obligations.

Rewrite using `[← chi_apply hPr σ₀ hr om mu eta xi0 w hi j (Units.map (resEquiv hPr hi).symm.toMonoidHom a) a ((resEquiv hPr hi).apply_symm_apply _), ← chi_apply hPr σ₀ hr om mu eta xi0 w hi j' (Units.map (resEquiv hPr hi).symm.toMonoidHom a) a ((resEquiv hPr hi).apply_symm_apply _)]`. Conclude with `DFunLike.congr_fun h _`. Conclude with `Fin.ext (by omega)`. Introduce `i w w' hi hi' j a x x' hx hx'`. Rewrite using `[chi_apply hPr σ₀ hr om mu eta xi0 w hi j x (Units.map (resEquiv hPr hi).toMonoidHom x) rfl, chi_apply hPr σ₀ hr om mu eta xi0 w' hi' j x' (Units.map (resEquiv hPr hi).toMonoidHom x)]`.

Use `show resEquiv hPr hi' x' = resEquiv hPr hi x`. Rewrite using `[hx, hx', map_intCast, map_intCast]`. Introduce `i w w' hi hi' a`. Rewrite using `[local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi, local_additive_char_apply hPr σ₀ hr om mu eta xi0 w' hi', map_mul (resEquiv hPr hi), map_mul (resEquiv hPr hi'), map_intCast (resEquiv hPr hi), map_intCast (resEquiv hPr hi'), red_same hX hPr hi hi' (resEquiv hPr hi) (resEq …`. Introduce `i`.

Use `⟨omK σ₀ (hPr.g_prime i) (hr i) (om i), omK_injective _ _ _ (hom i), fun w hi j a x hx => ?_⟩` and prove the remaining obligations. Use `Fact.mk (hPr.g_prime i)` as an intermediate fact. Conclude with `chi_apply hPr σ₀ hr om mu eta xi0 w hi j x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])`.
-/
theorem trueChars_ok (hX : X.Ok) (hom : ∀ i, Function.Injective (om i)) (hm : ∀ i, 2 * m < Pr.g i - 1)
    (hK : xi0 ∈ X.Kq) (hxi : XiUnitAt Pr.vGs xi0) : (trueChars hPr σ₀ hr om mu eta xi0).Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w h
    have hi := idx_mem w
    have := Fact.mk (hPr.g_prime (idx w))
    have h0 : resEquiv hPr hi (redP w.1 xi0) ≠ 0 := fun h0 =>
      (hxi w).2 ((resEquiv hPr hi).injective (by rw [h0, map_zero]))
    have h1 := local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi ((resEquiv hPr hi).symm (resEquiv hPr hi (redP w.1 xi0))⁻¹)
    rw [h, map_mul, RingEquiv.apply_symm_apply, mul_inv_cancel₀ h0] at h1
    exact psiK_one σ₀ _ _ h1.symm
  · intro w j j' h
    have hi := idx_mem w
    have hj := j.2
    have hj' := j'.2
    have hmi := hm (idx w)
    have h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1) := by
      refine GlobalTheory.BaseChars.eq_of_pow_eq (hPr.g_prime _) (omK_injective σ₀ (hPr.g_prime _) (hr _) (hom (idx w)))
        (by omega) (by omega) fun a => ?_
      rw [← chi_apply hPr σ₀ hr om mu eta xi0 w hi j (Units.map (resEquiv hPr hi).symm.toMonoidHom a) a
          ((resEquiv hPr hi).apply_symm_apply _),
        ← chi_apply hPr σ₀ hr om mu eta xi0 w hi j' (Units.map (resEquiv hPr hi).symm.toMonoidHom a) a
          ((resEquiv hPr hi).apply_symm_apply _)]
      exact DFunLike.congr_fun h _
    exact Fin.ext (by omega)
  · intro i w w' hi hi' j a x x' hx hx'
    rw [chi_apply hPr σ₀ hr om mu eta xi0 w hi j x (Units.map (resEquiv hPr hi).toMonoidHom x) rfl,
      chi_apply hPr σ₀ hr om mu eta xi0 w' hi' j x' (Units.map (resEquiv hPr hi).toMonoidHom x)]
    show resEquiv hPr hi' x' = resEquiv hPr hi x
    rw [hx, hx', map_intCast, map_intCast]
  · intro i w w' hi hi' a
    rw [local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi, local_additive_char_apply hPr σ₀ hr om mu eta xi0 w' hi', map_mul (resEquiv hPr hi), map_mul (resEquiv hPr hi'),
      map_intCast (resEquiv hPr hi), map_intCast (resEquiv hPr hi'),
      red_same hX hPr hi hi' (resEquiv hPr hi) (resEquiv hPr hi') hK (hxi w).1 (hxi w').1]
  · intro i
    refine ⟨omK σ₀ (hPr.g_prime i) (hr i) (om i), omK_injective _ _ _ (hom i), fun w hi j a x hx => ?_⟩
    have := Fact.mk (hPr.g_prime i)
    exact chi_apply hPr σ₀ hr om mu eta xi0 w hi j x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])

/- English proof (translation)
Introduce `w c b h`. Establish `hi` using `idx_mem w`. Rewrite using `[local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi, h, map_intCast, psiK_spec]`. Unfold `qOf`. Rewrite using `[hPr.vG_norm _ w.1 hi]`.
-/
theorem trueChars_weil : (trueChars hPr σ₀ hr om mu eta xi0).WeilTied σ₀ xi0 := by
  intro w c b h
  have hi := idx_mem w
  rw [local_additive_char_apply hPr σ₀ hr om mu eta xi0 w hi, h, map_intCast, psiK_spec]
  unfold qOf
  rw [hPr.vG_norm _ w.1 hi]

/- English proof (translation)
Use `mul_ne_zero (Units.ne_zero _) fun h => ?_` and prove the remaining obligations. Establish `h1` using `((Complex.cpow_eq_zero_iff _ _).1 h).1`. Conclude with `v.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))`.
-/
theorem valTw_ne_zero {L : Type} [Field L] [NumberField L] (χ : HChar L) (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) :
    χ.valTw s v ≠ 0 := by
  refine mul_ne_zero (Units.ne_zero _) fun h => ?_
  have h1 := ((Complex.cpow_eq_zero_iff _ _).1 h).1
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

/- English proof (translation)
Use `⟨fun j => ⟨hun j, htr j, hinf j, hunr j, htame j, ?_⟩, fun j v hv => ?_, heta, fun v => ?_⟩` and prove the remaining obligations. Introduce `w x y c hx hc`. Establish `hi` using `idx_mem w`. Use `Fact.mk (hPr.g_prime (idx w))` as an intermediate fact. Use `set a : (ZMod (Pr.g (idx w)))ˣ := Units.map (resEquiv hPr hi).toMonoidHom c with ha`.

Establish `ha' : resEquiv hPr hi c = a` using `rfl`. Establish `hn : (c : 𝓞 X.E ⧸ w.1.asIdeal) = ((a : ZMod (Pr.g (idx w))).val : ℕ)` using `(resEquiv hPr hi).injective (by rw [map_natCast, ZMod.natCast_zmod_val, ha'])`. Establish `hco` using `ZMod.val_coe_unit_coprime a`. Establish `hnot : (((a : ZMod (Pr.g (idx w))).val : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal` using `fun h => by`. Establish `h1` using `Ideal.Quotient.eq_zero_iff_mem.2 h`.

Rewrite `h1` using `[map_natCast, ← hn]`. Use `w.1.isPrime` as an intermediate fact. Conclude with `c.ne_zero h1`. Establish `hne : (((a : ZMod (Pr.g (idx w))).val : ℕ) : X.E) ≠ 0`. Introduce `h`.

Apply `hnot` to reduce the goal to its premises. Establish `h1 : (a : ZMod (Pr.g (idx w))).val = 0` using `by exact_mod_cast h`. Rewrite using `[h1, Nat.cast_zero]`. Conclude with `zero_mem _`. Establish `h1` using `locK_congr (mu j) w.1 (htame j w.1) x (Units.mk0 _ hne) y (((a : ZMod (Pr.g (idx w))).val : ℕ) : 𝓞 X.E) hx (map_natCast (algebraMap (𝓞 X.E) X.E) _).symm hnot (by rw [← Ideal.Quotient.eq, map_natCast, ← hn, hc])`.

Establish `h2 : ZMod.unitOfCoprime _ hco = a` using `Units.ext (by rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val])`. Rewrite using `[h1, hatg j _ w.1 hi _ hco _ rfl, h2, chi_apply hPr σ₀ hr om mu eta xi0 w hi j c a ha']`. Rewrite using `[Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, omK_spec]`. Establish `h1` using `pullUnit_spec σ₀ (valTw_ne_zero (mu j) 0 v) (hmuV j v (hunr j v hv))`. Use `h1.trans ?_` and prove the remaining obligations.

Simplify using `[Formalism.L2.Host.HChar.valTw]`. Conclude with `pullUnit_spec σ₀ (valTw_ne_zero eta _ v) (hetaV v (heta.unr v))`.
-/
theorem trueChars_tied (e : Fin m → X.Tau → ℚ) (heta : IsEtaT X σ₀ eta)
    (hun : ∀ j, (mu j).IsUnitary) (htr : ∀ j, (mu j).TrivOn X.F)
    (hinf : ∀ j, (mu j).HasInfQ (X.embC σ₀) (fun τ => -e j τ))
    (hunr : ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) → (mu j).UnrAt v)
    (htame : ∀ j v, (mu j).TameAt v)
    (hatg : ∀ (j : Fin m) (i : Fin 2), ∀ w ∈ Pr.vG i, ∀ (a : ℕ) (ha : a.Coprime (Pr.g i)) (x : X.Eˣ),
      (x : X.E) = (a : X.E) → (mu j).locK w x = (om i (ZMod.unitOfCoprime a ha) ^ (2 * (j.1 + 1)))⁻¹)
    (hmuV : ∀ j, (mu j).ValuesIn 0 σ₀) (hetaV : eta.ValuesIn (1 / 2) σ₀) :
    (trueChars hPr σ₀ hr om mu eta xi0).Tied σ₀ e mu eta := by
  refine ⟨fun j => ⟨hun j, htr j, hinf j, hunr j, htame j, ?_⟩, fun j v hv => ?_, heta, fun v => ?_⟩
  · intro w x y c hx hc
    have hi := idx_mem w
    have := Fact.mk (hPr.g_prime (idx w))
    set a : (ZMod (Pr.g (idx w)))ˣ := Units.map (resEquiv hPr hi).toMonoidHom c with ha
    have ha' : resEquiv hPr hi c = a := rfl
    have hn : (c : 𝓞 X.E ⧸ w.1.asIdeal) = ((a : ZMod (Pr.g (idx w))).val : ℕ) :=
      (resEquiv hPr hi).injective (by rw [map_natCast, ZMod.natCast_zmod_val, ha'])
    have hco := ZMod.val_coe_unit_coprime a
    have hnot : (((a : ZMod (Pr.g (idx w))).val : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal := fun h => by
      have h1 := Ideal.Quotient.eq_zero_iff_mem.2 h
      rw [map_natCast, ← hn] at h1
      have := w.1.isPrime
      exact c.ne_zero h1
    have hne : (((a : ZMod (Pr.g (idx w))).val : ℕ) : X.E) ≠ 0 := by
      intro h
      apply hnot
      have h1 : (a : ZMod (Pr.g (idx w))).val = 0 := by exact_mod_cast h
      rw [h1, Nat.cast_zero]
      exact zero_mem _
    have h1 := locK_congr (mu j) w.1 (htame j w.1) x (Units.mk0 _ hne) y
      (((a : ZMod (Pr.g (idx w))).val : ℕ) : 𝓞 X.E) hx (map_natCast (algebraMap (𝓞 X.E) X.E) _).symm hnot
      (by rw [← Ideal.Quotient.eq, map_natCast, ← hn, hc])
    have h2 : ZMod.unitOfCoprime _ hco = a := Units.ext (by rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val])
    rw [h1, hatg j _ w.1 hi _ hco _ rfl, h2, chi_apply hPr σ₀ hr om mu eta xi0 w hi j c a ha']
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      map_inv₀, map_pow, omK_spec]
  · have h1 := pullUnit_spec σ₀ (valTw_ne_zero (mu j) 0 v) (hmuV j v (hunr j v hv))
    refine h1.trans ?_
    simp [Formalism.L2.Host.HChar.valTw]
  · exact pullUnit_spec σ₀ (valTw_ne_zero eta _ v) (hetaV v (heta.unr v))

end Props

/- English proof (translation)
Assemble the required witnesses or components as `⟨trueChars hPr σ₀ hr om mu eta xi0, trueChars_ok hPr σ₀ hr om mu eta xi0 hX hom (fun i => by have := hm i; omega) hK fun w => unit_of_valuation w.1 (hxi w.1 w.2), trueChars_tied hPr σ₀ hr om mu eta xi0 e heta hun htr hinf hunr htame hatg hmuV hetaV, trueChars_weil hPr σ₀ hr om mu …`.
-/
theorem exists_trueChars (X : Fields) (Pr : Primes X) (hX : X.Ok) (hPr : Pr.Ok) (m : ℕ) (σ₀ : X.K →+* ℂ)
    (e : Fin m → X.Tau → ℚ) (mu : Fin m → HChar X.E) (eta : HChar X.E) (heta : IsEtaT X σ₀ eta)
    (om : ∀ i : Fin 2, (ZMod (Pr.g i))ˣ →* ℂˣ) (hom : ∀ i, Function.Injective (om i))
    (hm : ∀ i, 4 * m < Pr.g i - 1)
    (hun : ∀ j, (mu j).IsUnitary) (htr : ∀ j, (mu j).TrivOn X.F)
    (hinf : ∀ j, (mu j).HasInfQ (X.embC σ₀) (fun τ => -e j τ))
    (hunr : ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) → (mu j).UnrAt v)
    (htame : ∀ j v, (mu j).TameAt v)
    (hatg : ∀ (j : Fin m) (i : Fin 2), ∀ w ∈ Pr.vG i, ∀ (a : ℕ) (ha : a.Coprime (Pr.g i)) (x : X.Eˣ),
      (x : X.E) = (a : X.E) → (mu j).locK w x = (om i (ZMod.unitOfCoprime a ha) ^ (2 * (j.1 + 1)))⁻¹)
    (hmuV : ∀ j, (mu j).ValuesIn 0 σ₀) (hetaV : eta.ValuesIn (1 / 2) σ₀)
    (hr : ∀ (i : Fin 2) (z : ℂ), z ^ (Pr.g i * (Pr.g i - 1)) = 1 → ∃ y, σ₀ y = z)
    (xi0 : X.E) (hK : xi0 ∈ X.Kq) (hxi : ∀ w ∈ Pr.vGs, w.valuation X.E xi0 = 1) :
    ∃ Ch : Chars X Pr m, Ch.Ok ∧ Ch.Tied σ₀ e mu eta ∧ Ch.WeilTied σ₀ xi0 :=
  ⟨trueChars hPr σ₀ hr om mu eta xi0,
    trueChars_ok hPr σ₀ hr om mu eta xi0 hX hom (fun i => by have := hm i; omega) hK
      fun w => unit_of_valuation w.1 (hxi w.1 w.2),
    trueChars_tied hPr σ₀ hr om mu eta xi0 e heta hun htr hinf hunr htame hatg hmuV hetaV,
    trueChars_weil hPr σ₀ hr om mu eta xi0⟩

end GlobalTheory.TrueChars
