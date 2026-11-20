import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EvalTwistTxEqZeroOfAevalArcTx
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetConditionStatement

namespace GlobalTheory.Ex.OneLevel
section Arith
open Polynomial

/- English proof (translation)
Take `⟨y, hy⟩` from `y`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `rfl : x = z` from `hx`. Conclude with `⟨0, Subtype.ext (by simp [hz])⟩`.

Consider the case `algebraMap r => haveI := Fact.mk hd`. Establish `h : (d : ℤ) ∣ r ^ d ^ k - r`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card_pow, sub_self]`.

Use `map_dvd (algebraMap ℤ (Algebra.adjoin ℤ {z})) h` as an intermediate fact. Rewrite `this` using `[map_natCast, map_sub, map_pow]`. Then use the resulting hypothesis. Consider the case `add x y hx hy ihx ihy`. Express the relevant statement in the definitionally equal form `_ ∣ ((⟨x, hx⟩ + ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ + ⟨y, hy⟩)`. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hd (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) ⟨y, hy⟩ k`.

Rewrite using `[hr]`. Generalize the expression as in `(⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *`. Generalize the expression as in `(⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *`. Take `⟨s, hs⟩` from `ihx`. Take `⟨t, ht⟩` from `ihy`.

Conclude with `⟨s + t + a * b * r, by linear_combination hs + ht⟩`. Consider the case `mul x y hx hy ihx ihy`. Express the relevant statement in the definitionally equal form `_ ∣ ((⟨x, hx⟩ * ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ * ⟨y, hy⟩)`. Generalize the expression as in `(⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *`. Generalize the expression as in `(⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *`.

Take `⟨s, hs⟩` from `ihx`. Take `⟨t, ht⟩` from `ihy`. Conclude with `⟨s * b ^ d ^ k + a * t, by rw [mul_pow]; linear_combination b ^ d ^ k * hs + a * ht⟩`.
-/
theorem dvd_pow_sub {z : ℂ} {d k : ℕ} (hd : d.Prime) (hz : z ^ d ^ k = z) (y : Algebra.adjoin ℤ {z}) :
    (d : Algebra.adjoin ℤ {z}) ∣ y ^ d ^ k - y := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = z := hx
    exact ⟨0, Subtype.ext (by simp [hz])⟩
  | algebraMap r =>
    haveI := Fact.mk hd
    have h : (d : ℤ) ∣ r ^ d ^ k - r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.pow_card_pow, sub_self]
    have := map_dvd (algebraMap ℤ (Algebra.adjoin ℤ {z})) h
    rwa [map_natCast, map_sub, map_pow] at this
  | add x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ + ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ + ⟨y, hy⟩)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hd (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) ⟨y, hy⟩ k
    rw [hr]
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s + t + a * b * r, by linear_combination hs + ht⟩
  | mul x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ * ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ * ⟨y, hy⟩)
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s * b ^ d ^ k + a * t, by rw [mul_pow]; linear_combination b ^ d ^ k * hs + a * ht⟩

/- English proof (translation)
Establish `hc : d.Coprime N` using `(Nat.Prime.coprime_iff_not_dvd hd).2 hdN`. Establish `h1 : z ^ d ^ N.totient = z`. Use `pow_eq_pow_of_modEq (Nat.ModEq.pow_totient hc) hz` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `h2 : 2 ≤ d ^ N.totient` using `hd.two_le.trans (Nat.le_self_pow (Nat.totient_pos.2 hN).ne' d)`.

Establish `h3` using `dvd_sub (h.trans (pow_dvd_pow y h2)) (dvd_pow_sub hd h1 y)`. Rewrite `h3` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem dvd_of_dvd_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (y : Algebra.adjoin ℤ {z}) (h : (d : Algebra.adjoin ℤ {z}) ∣ y ^ 2) : (d : Algebra.adjoin ℤ {z}) ∣ y := by
  have hc : d.Coprime N := (Nat.Prime.coprime_iff_not_dvd hd).2 hdN
  have h1 : z ^ d ^ N.totient = z := by
    have := pow_eq_pow_of_modEq (Nat.ModEq.pow_totient hc) hz
    rwa [pow_one] at this
  have h2 : 2 ≤ d ^ N.totient := hd.two_le.trans (Nat.le_self_pow (Nat.totient_pos.2 hN).ne' d)
  have h3 := dvd_sub (h.trans (pow_dvd_pow y h2)) (dvd_pow_sub hd h1 y)
  rwa [sub_sub_cancel] at h3

/- English proof (translation)
Establish `hi : IsIntegral ℤ z` using `IsIntegral.of_pow hN (hz ▸ isIntegral_one)`. Use `haveI : Module.Finite ℤ (Algebra.adjoin ℤ {z}) := Algebra.finite_adjoin_simple_of_isIntegral hi`. Use `haveI : IsNoetherianRing (Algebra.adjoin ℤ {z}) := Algebra.FiniteType.isNoetherianRing ℤ _`. Establish `hd0 : (d : Algebra.adjoin ℤ {z}) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne_zero`. Establish `hu : ¬ IsUnit (d : Algebra.adjoin ℤ {z})` using `fun hu => by`.

Rewrite `hu` using `[← map_natCast (algebraMap ℤ (Algebra.adjoin ℤ {z}))]`. Conclude with `(Nat.prime_iff_prime_int.1 hd).not_unit (IsUnit.of_map _ _ hu)`. Proceed by induction on `B using (wellFounded_dvdNotUnit (α := Algebra.adjoin ℤ {z})).induction with`. Consider the case `_ B ih`. Introduce `A hA`.

Take `⟨A', rfl⟩` from `dvd_of_dvd_sq hd hN hdN hz A ⟨-B ^ 2, by rw [hA]; ring⟩`. Establish `h1 : B ^ 2 = d * -A' ^ 2` using `mul_left_cancel₀ hd0 (by linear_combination hA)`. Take `⟨B', rfl⟩` from `dvd_of_dvd_sq hd hN hdN hz B ⟨_, h1⟩`. Assume the negation of the conclusion as `h0`. Establish `hB' : B' ≠ 0` using `right_ne_zero_of_mul h0`.

Conclude with `hB' (ih B' ⟨hB', d, hu, mul_comm _ _⟩ A' (mul_left_cancel₀ hd0 (by linear_combination h1)))`.
-/
theorem eq_zero_of_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (B : Algebra.adjoin ℤ {z}) : ∀ A : Algebra.adjoin ℤ {z}, A ^ 2 = -d * B ^ 2 → B = 0 := by
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hN (hz ▸ isIntegral_one)
  haveI : Module.Finite ℤ (Algebra.adjoin ℤ {z}) := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsNoetherianRing (Algebra.adjoin ℤ {z}) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hd0 : (d : Algebra.adjoin ℤ {z}) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
  have hu : ¬ IsUnit (d : Algebra.adjoin ℤ {z}) := fun hu => by
    rw [← map_natCast (algebraMap ℤ (Algebra.adjoin ℤ {z}))] at hu
    exact (Nat.prime_iff_prime_int.1 hd).not_unit (IsUnit.of_map _ _ hu)
  induction B using (wellFounded_dvdNotUnit (α := Algebra.adjoin ℤ {z})).induction with
  | _ B ih =>
    intro A hA
    obtain ⟨A', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz A ⟨-B ^ 2, by rw [hA]; ring⟩
    have h1 : B ^ 2 = d * -A' ^ 2 := mul_left_cancel₀ hd0 (by linear_combination hA)
    obtain ⟨B', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz B ⟨_, h1⟩
    by_contra h0
    have hB' : B' ≠ 0 := right_ne_zero_of_mul h0
    exact hB' (ih B' ⟨hB', d, hu, mul_comm _ _⟩ A' (mul_left_cancel₀ hd0 (by linear_combination h1)))

/- English proof (translation)
Proceed by induction on `c using MvPolynomial.induction_on with`. Consider the case `C r => exact ⟨C r, 0, fun K _ ζ ρ _ => by simp⟩`. Consider the case `add p q hp hq`. Take `⟨a, b, h⟩` from `hp`. Take `⟨a', b', h'⟩` from `hq`.

Conclude with `⟨a + a', b + b', fun K _ ζ ρ e => by rw [map_add, h K ζ ρ e, h' K ζ ρ e, map_add, map_add]; ring⟩`. Consider the case `mul_X p i hp`. Take `⟨a, b, h⟩` from `hp`. Use `fin_cases i`. Conclude with `⟨a * X, b * X, fun K _ ζ ρ e => by rw [map_mul, h K ζ ρ e]; simp; ring⟩`.

Conclude with `⟨-d * b, a, fun K _ ζ ρ e => by`. Rewrite using `[map_mul, h K ζ ρ e]`. Simplify using the standard rewrite rules. Take the linear combination `aeval ζ b * e⟩`.
-/
theorem exists_linear (d : ℕ) (c : MvPolynomial (Fin 2) ℤ) : ∃ a b : ℤ[X], ∀ (K : Type) [CommRing K] (ζ ρ : K),
    ρ ^ 2 = -(d : K) → cf ζ ρ c = aeval ζ a + ρ * aeval ζ b := by
  induction c using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, fun K _ ζ ρ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨a', b', h'⟩ := hq
    exact ⟨a + a', b + b', fun K _ ζ ρ e => by rw [map_add, h K ζ ρ e, h' K ζ ρ e, map_add, map_add]; ring⟩
  | mul_X p i hp =>
    obtain ⟨a, b, h⟩ := hp
    fin_cases i
    · exact ⟨a * X, b * X, fun K _ ζ ρ e => by rw [map_mul, h K ζ ρ e]; simp; ring⟩
    · exact ⟨-d * b, a, fun K _ ζ ρ e => by
        rw [map_mul, h K ζ ρ e]; simp; linear_combination aeval ζ b * e⟩

/- English proof (translation)
Introduce `c hc`. Take `⟨a, b, h⟩` from `exists_linear H.d c`. Establish `hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N) N` using `Complex.isPrimitiveRoot_exp N hN.ne'`. Generalize the expression as in `ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = z at hc hz`. Rewrite `hc` using `[h ℂ _ _ H.sqrt_neg_disc_sq]`.

Establish `hb : aeval z b = 0` using `congrArg Subtype.val (eq_zero_of_sq H.d_prime hN hdN hz.pow_eq_one ⟨aeval z b, aeval_mem_adjoin_singleton _ _⟩ ⟨aeval z a, aeval_mem_adjoin_singleton _ _⟩ (Subtype.ext (by`. Use `H.sqrt_neg_disc_sq` as an intermediate fact. Use `push_cast`. Take the linear combination `(aeval z a - H.rt0 * aeval z b) * hc + aeval z b ^ 2 * this)))`. Establish `ha : aeval z a = 0` using `by rwa [hb, mul_zero, add_zero] at hc`.

Establish `key : ∀ p : ℤ[X], aeval z p = 0 → aeval ζ p = 0` using `fun p hp => by`. Establish `h1` using `minpoly.isIntegrallyClosed_dvd (hz.isIntegral hN) hp`. Rewrite `h1` using `[← cyclotomic_eq_minpoly hz hN]`. Use `aeval_eq_zero_of_dvd_aeval_eq_zero h1 ?_` and prove the remaining obligations. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`.

Conclude with `hζ.isRoot_cyclotomic hN`. Rewrite using `[h K _ _ hρ, key a ha, key b hb, mul_zero, add_zero]`.
-/
theorem compat_of_not_dvd {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {N : ℕ} (hN : 0 < N) (hdN : ¬ H.d ∣ N) {K : Type} [Field K] {ζ ρ : K}
    (hζ : IsPrimitiveRoot ζ N) (hρ : ρ ^ 2 = -(H.d : K)) : Compat H N ζ ρ := by
  intro c hc
  obtain ⟨a, b, h⟩ := exists_linear H.d c
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N) N := Complex.isPrimitiveRoot_exp N hN.ne'
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = z at hc hz
  rw [h ℂ _ _ H.sqrt_neg_disc_sq] at hc
  have hb : aeval z b = 0 := congrArg Subtype.val (eq_zero_of_sq H.d_prime hN hdN hz.pow_eq_one
    ⟨aeval z b, aeval_mem_adjoin_singleton _ _⟩ ⟨aeval z a, aeval_mem_adjoin_singleton _ _⟩ (Subtype.ext (by
      have := H.sqrt_neg_disc_sq
      push_cast
      linear_combination (aeval z a - H.rt0 * aeval z b) * hc + aeval z b ^ 2 * this)))
  have ha : aeval z a = 0 := by rwa [hb, mul_zero, add_zero] at hc
  have key : ∀ p : ℤ[X], aeval z p = 0 → aeval ζ p = 0 := fun p hp => by
    have h1 := minpoly.isIntegrallyClosed_dvd (hz.isIntegral hN) hp
    rw [← cyclotomic_eq_minpoly hz hN] at h1
    refine aeval_eq_zero_of_dvd_aeval_eq_zero h1 ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hN
  rw [h K _ _ hρ, key a ha, key b hb, mul_zero, add_zero]
end Arith

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (j : ℕ) (hj : 0 < j) : N.Form j where
  be := (j : ℤ) • β.be
  symm y z := congrArg ((j : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hj) (β.pos y hy)
  dvd y z := by
    change _ ∣ (j : ℤ) * β.be y z
    rw [mul_comm 2]
    exact mul_dvd_mul_left _ ((Dvd.intro _ rfl).trans (β.dvd y z))

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[show p = p' from Subtype.ext (Prod.ext h1 (NumD.Gt.ext h2 h3))]`.
-/
theorem tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) (ψ ψ' : N.X → Oˣ) (e b e' b') (h : ψ = ψ')
    (m : ℕ) (p : ({ N with ψ := ψ, even := e, bimult := b } : NumD O).QT (m ^ 2))
    (p' : ({ N with ψ := ψ', even := e', bimult := b' } : NumD O).QT (m ^ 2))
    (h1 : p.1.1 = p'.1.1) (h2 : p.1.2.b = p'.1.2.b) (h3 : p.1.2.s = p'.1.2.s) :
    NumD.tx _ m p = NumD.tx _ m p' := by
  subst h
  rw [show p = p' from Subtype.ext (Prod.ext h1 (NumD.Gt.ext h2 h3))]

/- English proof (translation)
Use `tx_congr N _ _ _ _ _ _ (funext fun χ => ?_) m _ _ h.1 h.2.1 (funext fun χ => (h.2.2 χ).trans ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be χ χ / 2)`. Rewrite using `[Int.mul_ediv_assoc _ ((Dvd.intro _ rfl).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, hr]`. Express the relevant statement in the definitionally equal form `_ = q.1.2.s χ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be q.1.1.toAdd χ / ((m ^ 2 : ℕ) : ℤ))`. Rewrite using `[Int.mul_ediv_cancel_left _ (Int.natCast_pos.2 hm).ne']`.
-/
theorem tx_scale {O : Type} [CommRing O] [TopologicalSpace O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ)
    (hm : 0 < m ^ 2) (u r : Oˣ) (hr : r ^ m ^ 2 = u) (q : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2))
    (h : TwRel β u r q p) :
    (N.twist β u).tx m p =
      (N.twist (scaleForm β _ hm) r).tx m (N.twQ (scaleForm β _ hm) r dvd_rfl q) := by
  refine tx_congr N _ _ _ _ _ _ (funext fun χ => ?_) m _ _ h.1 h.2.1 (funext fun χ => (h.2.2 χ).trans ?_)
  · change _ = _ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, hr]
  · change _ = q.1.2.s χ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be q.1.1.toAdd χ / ((m ^ 2 : ℕ) : ℤ))
    rw [Int.mul_ediv_cancel_left _ (Int.natCast_pos.2 hm).ne']

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `h` using `hG (MvPolynomial.mem_support_iff.1 he)`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[← h, Finsupp.weight_apply]`.

Simplify using `only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_mul_of_isHomogeneous {ι C : Type} [CommRing C] {G : MvPolynomial ι C} {d : ℕ} (hG : G.IsHomogeneous d)
    (s : C) (v : ι → C) : MvPolynomial.eval (fun i => s * v i) G = s ^ d * MvPolynomial.eval v G := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := hG (MvPolynomial.mem_support_iff.1 he)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← h, Finsupp.weight_apply]
  simp only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  ring
end GlobalTheory.Ex.OneLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.OneLevel

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ _ S n j hn ho hu hd hj`. Use `haveI : CharZero K := S.A.arc.charZero`. Establish `hm : Odd (n ^ j)` using `ho.pow`. Establish `hm2 : 0 < (n ^ j) ^ 2` using `pow_pos hm.pos 2`. Establish `hdN : ¬ H.d ∣ (n ^ j) ^ 2` using `fun h => hd (by`.

Rewrite using `[(Nat.prime_dvd_prime_iff_eq H.d_prime hn).1 (H.d_prime.dvd_of_dvd_pow (H.d_prime.dvd_of_dvd_pow h))])`. Take `⟨o, e1, e2, e3⟩` from `GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K n j S.A.ρ (S.A.I.ζ ((n ^ j) ^ 2)) (S.v (n ^ j)) hn ho hj (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (S.A.I.ζ_prim _ hm2)) S.A.ρ_sq) (fun G hG => by_contra fun hne …`. Take `⟨A', r', i1, ⟨_, o1, o2, -⟩, i3, i4⟩` from `S.val C gam u c1 c2 c3 c4`. Use `haveI : CharZero C := A'.arc.charZero`. Establish `hr : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = u` using `Units.ext (by`.

Rewrite using `[Units.val_pow_eq_pow_val, i3, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.pow hm2, S.r_one, c3]`. Use the proof step `rfl)`. Establish `hr1 : ‖(r' ((n ^ j) ^ 2) : C)‖ < 1`. Rewrite `c4` using `[← hr, Units.val_pow_eq_pow_val, norm_pow]`. Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) hm2.ne').1 c4`.

Use `choose p hp using fun x => (existsUnique_twRel A'.be u _ hr (A'.q _ x)).exists`. Take `⟨⟨s, hs⟩, -⟩` from `i4 _ hm p hp`. Establish `hbal : A'.arc.Bal (scaleForm A'.be _ hm2)` using `fun x y z => by`. Use `congrArg ((((n ^ j) ^ 2 : ℕ) : ℤ) * ·) ((A'.be_eq _ _).trans (Eq.trans ?_ (A'.be_eq _ _).symm))` and prove the remaining obligations. Use `(congrArg (a.be · _) (A'.ν.eX.apply_symm_apply _)).trans ((a.be_adj _ _ _).trans ?_)` and prove the remaining obligations.

Conclude with `congrArg (a.be _ ·) (A'.ν.eX.apply_symm_apply _).symm`. Establish `k1` using `GlobalTheory.T.theta_series_identity_principle_complex_points h1 h2 h3 h4 h5 h6 h7 E H D O' C A'.arc _ (scaleForm A'.be _ hm2) hbal _ dvd_rfl hm (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (A'.I.ζ_prim _ hm2)) A'.ρ_sq) G hG`. Establish `hC : CExt O' ⊥ C` using `⟨fun x => by rw [c1]; exact c2 _, fun x hx => by`. Rewrite using `[(Submodule.mem_bot _).1 hx, map_zero, map_zero, norm_zero]`. Conclude with `one_pos⟩`.

Establish `k2` using `GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx C A'.N _ (scaleForm A'.be _ hm2) _ dvd_rfl hm D.La (A'.q _) (fun x => (GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hC A' i1).2.1 _ hm _) _ k1 _ hr1`. Take `⟨d, hGd⟩` from `hG.2.1`. Apply `gam.injective` to reduce the goal to its premises. Establish `ec : gam.comp (cf (S.A.I.ζ ((n ^ j) ^ 2) : K) S.A.ρ) = cf (A'.I.ζ ((n ^ j) ^ 2) : C) A'.ρ`. Use `MvPolynomial.ringHom_ext (fun x => by simp) fun i => ?_` and prove the remaining obligations.

Use `fin_cases i`. Simplify `o2 _ hm2` using `[Lift.arc]`. Simplify `o1` using `[Lift.arc]`. Rewrite using `[map_zero, MvPolynomial.eval₂_comp_left, ec, MvPolynomial.eval₂_eq_eval_map]`. Establish `ev : gam ∘ S.v (n ^ j) = fun x => (s : C) * (A'.N.twist (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2))).tx (n ^ j) (A'.N.twQ (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2)) dvd_rfl (A'.q _ x))` using `funext fun x => (hs x).trans (congrArg _ (tx_scale A'.be _ hm2 u _ hr _ _ (hp x)))`.

Rewrite using `[ev, eval_mul_of_isHomogeneous (hGd.map _)]`. Conclude with `mul_eq_zero_of_right _ k2))`. Use the proof step `(fun x => by`. Establish `hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0` using `by rw [← S.r_one]; exact Units.ne_zero _`. Take `⟨h, hh⟩` from `(S.int n j hn ho hu (by omega) ⊤ fun _ => trivial).2.2 ((ValuationSubring.valuation_eq_one_iff (⊤ : ValuationSubring K) ⟨_, trivial⟩).1 (IsUnit.of_mul_eq_one ⟨_⁻¹, trivial⟩ (Subtype.ext (mul_inv_cancel₀ hX)))) x`.

Conclude with `⟨h, fun e => by rw [e, map_zero] at hh; exact zero_ne_one hh⟩)`. Conclude with `⟨o, e1, Units.ext e2, e3⟩`.
-/
theorem exists_full_theta : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ _ S n j hn ho hu hd hj
  haveI : CharZero K := S.A.arc.charZero
  have hm : Odd (n ^ j) := ho.pow
  have hm2 : 0 < (n ^ j) ^ 2 := pow_pos hm.pos 2
  have hdN : ¬ H.d ∣ (n ^ j) ^ 2 := fun h => hd (by
    rw [(Nat.prime_dvd_prime_iff_eq H.d_prime hn).1 (H.d_prime.dvd_of_dvd_pow (H.d_prime.dvd_of_dvd_pow h))])
  obtain ⟨o, e1, e2, e3⟩ := GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K n j S.A.ρ
    (S.A.I.ζ ((n ^ j) ^ 2)) (S.v (n ^ j)) hn ho hj
    (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (S.A.I.ζ_prim _ hm2)) S.A.ρ_sq)
    (fun G hG => by_contra fun hne => S.base.not_allC_false fun C _ _ _ _ _ gam u c1 c2 c3 c4 => hne (by
      obtain ⟨A', r', i1, ⟨_, o1, o2, -⟩, i3, i4⟩ := S.val C gam u c1 c2 c3 c4
      haveI : CharZero C := A'.arc.charZero
      have hr : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = u := Units.ext (by
        rw [Units.val_pow_eq_pow_val, i3, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.pow hm2, S.r_one, c3]; rfl)
      have hr1 : ‖(r' ((n ^ j) ^ 2) : C)‖ < 1 := by
        rw [← hr, Units.val_pow_eq_pow_val, norm_pow] at c4
        exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hm2.ne').1 c4
      choose p hp using fun x => (existsUnique_twRel A'.be u _ hr (A'.q _ x)).exists
      obtain ⟨⟨s, hs⟩, -⟩ := i4 _ hm p hp
      have hbal : A'.arc.Bal (scaleForm A'.be _ hm2) := fun x y z => by
        refine congrArg ((((n ^ j) ^ 2 : ℕ) : ℤ) * ·) ((A'.be_eq _ _).trans (Eq.trans ?_ (A'.be_eq _ _).symm))
        refine (congrArg (a.be · _) (A'.ν.eX.apply_symm_apply _)).trans ((a.be_adj _ _ _).trans ?_)
        exact congrArg (a.be _ ·) (A'.ν.eX.apply_symm_apply _).symm
      have k1 := GlobalTheory.T.theta_series_identity_principle_complex_points h1 h2 h3 h4 h5 h6 h7 E H D O' C A'.arc _ (scaleForm A'.be _ hm2) hbal _ dvd_rfl hm
        (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (A'.I.ζ_prim _ hm2)) A'.ρ_sq) G hG
      have hC : CExt O' ⊥ C := ⟨fun x => by rw [c1]; exact c2 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
      have k2 := GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx C A'.N _ (scaleForm A'.be _ hm2) _ dvd_rfl hm D.La (A'.q _)
        (fun x => (GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hC A' i1).2.1 _ hm _) _ k1 _ hr1
      obtain ⟨d, hGd⟩ := hG.2.1
      apply gam.injective
      have ec : gam.comp (cf (S.A.I.ζ ((n ^ j) ^ 2) : K) S.A.ρ) = cf (A'.I.ζ ((n ^ j) ^ 2) : C) A'.ρ := by
        refine MvPolynomial.ringHom_ext (fun x => by simp) fun i => ?_
        fin_cases i
        · simpa [Lift.arc] using o2 _ hm2
        · simpa [Lift.arc] using o1
      rw [map_zero, MvPolynomial.eval₂_comp_left, ec, MvPolynomial.eval₂_eq_eval_map]
      have ev : gam ∘ S.v (n ^ j) = fun x => (s : C) * (A'.N.twist (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2))).tx (n ^ j)
          (A'.N.twQ (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2)) dvd_rfl (A'.q _ x)) := funext fun x =>
        (hs x).trans (congrArg _ (tx_scale A'.be _ hm2 u _ hr _ _ (hp x)))
      rw [ev, eval_mul_of_isHomogeneous (hGd.map _)]
      exact mul_eq_zero_of_right _ k2))
    (fun x => by
      have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := by rw [← S.r_one]; exact Units.ne_zero _
      obtain ⟨h, hh⟩ := (S.int n j hn ho hu (by omega) ⊤ fun _ => trivial).2.2
        ((ValuationSubring.valuation_eq_one_iff (⊤ : ValuationSubring K) ⟨_, trivial⟩).1
          (IsUnit.of_mul_eq_one ⟨_⁻¹, trivial⟩ (Subtype.ext (mul_inv_cancel₀ hX)))) x
      exact ⟨h, fun e => by rw [e, map_zero] at hh; exact zero_ne_one hh⟩)
  exact ⟨o, e1, Units.ext e2, e3⟩
end GlobalTheory.Ex.OneLevel
