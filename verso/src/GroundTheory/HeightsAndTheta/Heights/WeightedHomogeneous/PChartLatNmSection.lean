import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatNm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hf'` using `(geoMultiHomog_iff f d).mpr hf`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf' m hm k]`.

Simplify using `only [Geo.mConeMap, aeval_monomial]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_of_homog (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
  have hf' := (geoMultiHomog_iff f d).mpr hf
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [Geo.mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hf, mul_eq_zero, C_eq_zero]`. Establish `: (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)`. Simplify using `[this]`.
-/
theorem mem_mCoordIdeal_iff (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hf, mul_eq_zero, C_eq_zero]
  have : (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
  simp [this]

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k) (fun k => e k • coordDeg n ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ (coordDeg n) _).pow (e k))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `[coordDeg, Finset.sum_apply, Pi.single_apply]`.
-/
theorem isWeightedHomogeneous_chartMono (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    IsWeightedHomogeneous (coordDeg n) (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k) e := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k)
    (fun k => e k • coordDeg n ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ (coordDeg n) _).pow (e k))
  convert h using 1
  funext j
  simp [coordDeg, Finset.sum_apply, Pi.single_apply]

variable (P : ArithVariety n) (y : Coord n → Ω)

/- English proof (translation)
Rewrite using `[P.mkF_eq_zero_iff, hP, mem_mCoordIdeal_iff y hf]`.
-/
theorem mkF_eq_zero_iff' (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f d) :
    P.mkF f = 0 ↔ aeval y f = 0 := by
  rw [P.mkF_eq_zero_iff, hP, mem_mCoordIdeal_iff y hf]

/- English proof (translation)
Use `forall_congr' fun k => ?_` and prove the remaining obligations. Rewrite using `[hP, mem_mCoordIdeal_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩), aeval_X]`.
-/
theorem isLive_iff' (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1)) :
    P.IsLive c ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  rw [hP, mem_mCoordIdeal_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩), aeval_X]

/- English proof (translation)
Take `⟨d, g, h, hg, hh, h0, he⟩` from `hb s`. Conclude with `⟨g, h, d, (geoMultiHomog_iff g d).mp hg, (geoMultiHomog_iff h d).mp hh, h0, he⟩`.
-/
theorem exists_rep (hb : Geo.Birational (ι := blockIdx n) y) (s : Ω) :
    ∃ (g h : MvPolynomial (Coord n) ℤ) (d : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g d ∧
      IsWeightedHomogeneous (coordDeg n) h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h := by
  obtain ⟨d, g, h, hg, hh, h0, he⟩ := hb s
  exact ⟨g, h, d, (geoMultiHomog_iff g d).mp hg, (geoMultiHomog_iff h d).mp hh, h0, he⟩

/- English proof (translation)
Rewrite using `[div_eq_div_iff (fun h => hq₀0 ((mkF_eq_zero_iff' P y hP hq₀).mp h)) (fun h => h0 ((mkF_eq_zero_iff' P y hP hq).mp h))]`. Rewrite using `[← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]`. Establish `h1` using `hg₀.mul hq`. Establish `h2` using `hg.mul hq₀`. Rewrite `h2` using `[add_comm]`.

Establish `hsub : IsWeightedHomogeneous (coordDeg n) (g₀ * q - g * q₀) (d₀ + d)` using `(weightedHomogeneousSubmodule ℤ (coordDeg n) (d₀ + d)).sub_mem h1 h2`. Rewrite using `[mkF_eq_zero_iff' P y hP hsub, map_sub, map_mul, map_mul, he₀, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frac_eq (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) {s : Ω}
    {g q g₀ q₀ : MvPolynomial (Coord n) ℤ} {d d₀ : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q)
    (hg₀ : IsWeightedHomogeneous (coordDeg n) g₀ d₀) (hq₀ : IsWeightedHomogeneous (coordDeg n) q₀ d₀)
    (hq₀0 : aeval y q₀ ≠ 0) (he₀ : aeval y g₀ = s * aeval y q₀) :
    P.mkF g₀ / P.mkF q₀ = P.mkF g / P.mkF q := by
  rw [div_eq_div_iff (fun h => hq₀0 ((mkF_eq_zero_iff' P y hP hq₀).mp h))
    (fun h => h0 ((mkF_eq_zero_iff' P y hP hq).mp h))]
  rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]
  have h1 := hg₀.mul hq
  have h2 := hg.mul hq₀
  rw [add_comm] at h2
  have hsub : IsWeightedHomogeneous (coordDeg n) (g₀ * q - g * q₀) (d₀ + d) :=
    (weightedHomogeneousSubmodule ℤ (coordDeg n) (d₀ + d)).sub_mem h1 h2
  rw [mkF_eq_zero_iff' P y hP hsub, map_sub, map_mul, map_mul, he₀, he]
  ring

def thetaFun (hb : Geo.Birational (ι := blockIdx n) y) (s : Ω) : P.FunField :=
  P.mkF (exists_rep y hb s).choose / P.mkF (exists_rep y hb s).choose_spec.choose

/- English proof (translation)
Take `⟨d₀, hg₀, hq₀, hq₀0, he₀⟩` from `(exists_rep y hb s).choose_spec.choose_spec`. Conclude with `frac_eq P y hP hg hq h0 he hg₀ hq₀ hq₀0 he₀`.
-/
theorem thetaFun_eq (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    (hb : Geo.Birational (ι := blockIdx n) y) {s : Ω} {g q : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q) :
    thetaFun P y hb s = P.mkF g / P.mkF q := by
  obtain ⟨d₀, hg₀, hq₀, hq₀0, he₀⟩ := (exists_rep y hb s).choose_spec.choose_spec
  exact frac_eq P y hP hg hq h0 he hg₀ hq₀ hq₀0 he₀

def theta (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
    (hb : Geo.Birational (ι := blockIdx n) y) : Ω →+* P.FunField where
  toFun := thetaFun P y hb
  map_one' := by
    rw [thetaFun_eq P y hP hb (isWeightedHomogeneous_one ℤ (coordDeg n))
      (isWeightedHomogeneous_one ℤ (coordDeg n)) (by simp) (by simp)]
    simp
  map_zero' := by
    rw [thetaFun_eq P y hP hb (isWeightedHomogeneous_zero ℤ (coordDeg n) 0)
      (isWeightedHomogeneous_one ℤ (coordDeg n)) (by simp) (by simp)]
    simp
  map_mul' s s' := by
    obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb s
    obtain ⟨g', q', d', hg', hq', hq0', he'⟩ := exists_rep y hb s'
    rw [thetaFun_eq P y hP hb hg hq hq0 he, thetaFun_eq P y hP hb hg' hq' hq0' he',
      thetaFun_eq P y hP hb (hg.mul hg') (hq.mul hq') (by rw [map_mul]; exact mul_ne_zero hq0 hq0')
        (by rw [map_mul, map_mul, he, he']; ring), map_mul, map_mul, div_mul_div_comm]
  map_add' s s' := by
    obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb s
    obtain ⟨g', q', d', hg', hq', hq0', he'⟩ := exists_rep y hb s'
    have h2 := hg'.mul hq
    rw [add_comm] at h2
    have hQ0 : P.mkF q ≠ 0 := fun h => hq0 ((mkF_eq_zero_iff' P y hP hq).mp h)
    have hQ0' : P.mkF q' ≠ 0 := fun h => hq0' ((mkF_eq_zero_iff' P y hP hq').mp h)
    rw [thetaFun_eq P y hP hb hg hq hq0 he, thetaFun_eq P y hP hb hg' hq' hq0' he',
      thetaFun_eq P y hP hb ((hg.mul hq').add h2) (hq.mul hq')
        (by rw [map_mul]; exact mul_ne_zero hq0 hq0')
        (by simp only [map_add, map_mul]; rw [he, he']; ring)]
    rw [div_add_div _ _ hQ0 hQ0']
    simp only [map_add, map_mul]
    ring

/- English proof (translation)
Introduce `h` and use `hc k (by rw [← aeval_X (R := ℤ) y ⟨k, c k⟩] exact (mkF_eq_zero_iff' P y hP (isWeightedHomogeneous_X ℤ (coordDeg n) _)).mp h)`.
-/
theorem mkF_X_ne_zero (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : ι) : P.mkF (X ⟨k, c k⟩) ≠ 0 := fun h =>
  hc k (by
    rw [← aeval_X (R := ℤ) y ⟨k, c k⟩]
    exact (mkF_eq_zero_iff' P y hP (isWeightedHomogeneous_X ℤ (coordDeg n) _)).mp h)

/- English proof (translation)
Simplify using `only [ArithVariety.chartPow, Pi.add_apply, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => zpow_add₀ (mkF_X_ne_zero P y hP c hc k) _ _`.
-/
theorem chartPow_add (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : ι → ℤ) :
    P.chartPow c (e + e') = P.chartPow c e * P.chartPow c e' := by
  simp only [ArithVariety.chartPow, Pi.add_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (mkF_X_ne_zero P y hP c hc k) _ _

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (mkF_X_ne_zero P y hP c hc k)`.
-/
theorem chartPow_ne_zero (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ι → ℤ) : P.chartPow c e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (mkF_X_ne_zero P y hP c hc k)

/- English proof (translation)
Take `⟨g, q, d, hg, hq, hq0, he⟩` from `exists_rep y hb (s * ∏ k, y ⟨k, c₀ k⟩ ^ (-b k))`. Use `⟨g * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (b k).toNat, q * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (-b k).toNat, d + fun k => (b k).toNat, d + fun k => (-b k).toNat, hg.mul (isWeightedHomogeneous_chartMono c₀ _), hq.mul (isWeightedHomogeneous_chartMono c₀ _), f …` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [map_mul, map_prod, map_pow, aeval_X]`. Conclude with `mul_ne_zero hq0 (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k))`. Simplify using `only [map_mul, map_prod, map_pow, aeval_X]`. Rewrite using `[he]`. Establish `h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (b k).toNat = ∏ k, y ⟨k, c₀ k⟩ ^ (-b k).toNat`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc₀ k)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Take the linear combination `(s * aeval y q) * h1`.
-/
theorem exists_reads_rep (hb : Geo.Birational (ι := blockIdx n) y) (c₀ : (k : ι) → Fin (n k + 1))
    (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    ∃ (f q : MvPolynomial (Coord n) ℤ) (δf δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
      IsWeightedHomogeneous (coordDeg n) q δq ∧ (∀ k, (δf k : ℤ) = δq k + b k) ∧ aeval y q ≠ 0 ∧
      aeval y f = s * aeval y q := by
  obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb (s * ∏ k, y ⟨k, c₀ k⟩ ^ (-b k))
  refine ⟨g * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (b k).toNat,
    q * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (-b k).toNat, d + fun k => (b k).toNat,
    d + fun k => (-b k).toNat, hg.mul (isWeightedHomogeneous_chartMono c₀ _),
    hq.mul (isWeightedHomogeneous_chartMono c₀ _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    exact mul_ne_zero hq0 (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k))
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he]
    have h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (b k).toNat =
        ∏ k, y ⟨k, c₀ k⟩ ^ (-b k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc₀ k)]
      congr 1
      omega
    linear_combination (s * aeval y q) * h1

variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)

/- English proof (translation)
The claim follows from `thetaFun_eq P y hP hb hg hq h0 he`.
-/
theorem theta_eq {s : Ω} {g q : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}
    (hg : IsWeightedHomogeneous (coordDeg n) g d) (hq : IsWeightedHomogeneous (coordDeg n) q d)
    (h0 : aeval y q ≠ 0) (he : aeval y g = s * aeval y q) :
    theta P y hP hb s = P.mkF g / P.mkF q :=
  thetaFun_eq P y hP hb hg hq h0 he

/- English proof (translation)
Establish `hM` using `isWeightedHomogeneous_chartMono c δ`. Establish `hMy : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = ∏ k, y ⟨k, c k⟩ ^ δ k`. Simplify using `[map_prod]`. Establish `hMy0 : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0`. Rewrite using `[hMy]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `hMF : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = P.chartPow c (fun k => (δ k : ℤ))`. Simplify using `[ArithVariety.chartPow, map_prod, zpow_natCast]`. Establish `hne : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0` using `fun h => hMy0 ((mkF_eq_zero_iff' P y hP hM).mp h)`. Rewrite using `[theta_eq P y hP hb hg hM hMy0, ← hMF, div_mul_cancel₀ _ hne]`.

Rewrite using `[hMy, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by`. Rewrite using `[zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc k))]), mul_one]`.
-/
theorem mkF_eq_theta (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g δ) :
    P.mkF g = theta P y hP hb (aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ))) *
      P.chartPow c (fun k => (δ k : ℤ)) := by
  have hM := isWeightedHomogeneous_chartMono c δ
  have hMy : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = ∏ k, y ⟨k, c k⟩ ^ δ k := by
    simp [map_prod]
  have hMy0 : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0 := by
    rw [hMy]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hMF : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = P.chartPow c (fun k => (δ k : ℤ)) := by
    simp [ArithVariety.chartPow, map_prod, zpow_natCast]
  have hne : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0 :=
    fun h => hMy0 ((mkF_eq_zero_iff' P y hP hM).mp h)
  rw [theta_eq P y hP hb hg hM hMy0, ← hMF, div_mul_cancel₀ _ hne]
  rw [hMy, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc k))]), mul_one]

/- English proof (translation)
Rewrite using `[ArithVariety.chartCoord]`. Conclude with `theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) p) (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨p.1, c p.1⟩ : IsWeightedHomogeneous _ _ (coordDeg n p)) (by rw [aeval_X]; exact hc p.1) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc p.1)])`.
-/
theorem theta_chartCoord (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (p : Coord n) :
    theta P y hP hb (y p / y ⟨p.1, c p.1⟩) = P.chartCoord c p := by
  rw [ArithVariety.chartCoord]
  exact theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) p)
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨p.1, c p.1⟩ : IsWeightedHomogeneous _ _ (coordDeg n p))
    (by rw [aeval_X]; exact hc p.1) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc p.1)])

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib, map_prod, ArithVariety.chartPow, ArithVariety.chartPow, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, ← div_eq_mul_inv, ← div_zpow, map_zpow₀, ← div_zpow]`. Use `congr 1`. Conclude with `theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩) (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c' k⟩ : IsWeightedHomogeneous _ _ (coordDeg n ⟨k, c k⟩)) (by rw [aeval_X]; exact hc' k) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc' k)])`.
-/
theorem theta_chartRatio (c c' : (k : ι) → Fin (n k + 1)) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (e : ι → ℤ) :
    theta P y hP hb ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c' k⟩ ^ (-e k)) =
      P.chartPow c e / P.chartPow c' e := by
  rw [← Finset.prod_mul_distrib, map_prod, ArithVariety.chartPow, ArithVariety.chartPow,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_neg, ← div_eq_mul_inv, ← div_zpow, map_zpow₀, ← div_zpow]
  congr 1
  exact theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩)
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c' k⟩ :
      IsWeightedHomogeneous _ _ (coordDeg n ⟨k, c k⟩))
    (by rw [aeval_X]; exact hc' k) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc' k)])

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem u hu`. Take `⟨p, rfl⟩` from `hu`. Rewrite using `[theta_chartCoord P y hP hb c hc p]`. Conclude with `Subring.subset_closure ⟨p, rfl⟩`.

Consider the case `algebraMap r`. Rewrite using `[eq_intCast, map_intCast]`. Conclude with `intCast_mem _ r`. Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add]`.

Conclude with `add_mem hu hv`. Consider the case `mul u v _ _ hu hv`. Rewrite using `[map_mul]`. Conclude with `mul_mem hu hv`.
-/
theorem theta_mem_chartRing (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) : theta P y hP hb x ∈ P.chartRing c := by
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨p, rfl⟩ := hu
    rw [theta_chartCoord P y hP hb c hc p]
    exact Subring.subset_closure ⟨p, rfl⟩
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add u v _ _ hu hv =>
    rw [map_add]
    exact add_mem hu hv
  | mul u v _ _ hu hv =>
    rw [map_mul]
    exact mul_mem hu hv

/- English proof (translation)
Establish `hle : P.chartRing c ≤ (Geo.chartRingZ (ι` using `blockIdx n) y c).toSubring.map (theta P y hP hb) := by`. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `Subring.mem_map.mpr ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩, theta_chartCoord P y hP hb c hc p⟩`. Take `⟨x, hx, hxu⟩` from `Subring.mem_map.mp (hle hu)`.

Conclude with `⟨x, hx, hxu⟩`.
-/
theorem exists_theta_eq (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {u : P.FunField}
    (hu : u ∈ P.chartRing c) : ∃ x ∈ Geo.chartRingZ (ι := blockIdx n) y c, theta P y hP hb x = u := by
  have hle : P.chartRing c ≤ (Geo.chartRingZ (ι := blockIdx n) y c).toSubring.map (theta P y hP hb) := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact Subring.mem_map.mpr ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩, theta_chartCoord P y hP hb c hc p⟩
  obtain ⟨x, hx, hxu⟩ := Subring.mem_map.mp (hle hu)
  exact ⟨x, hx, hxu⟩

def thetaChart (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Geo.chartRingZ (ι := blockIdx n) y c →+* P.chartRing c :=
  ((theta P y hP hb).comp (Geo.chartRingZ (ι := blockIdx n) y c).val.toRingHom).codRestrict
    (P.chartRing c) fun x => theta_mem_chartRing P y hP hb c hc x.2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `hinj : Function.Injective (thetaChart P y hP hb c hc)` using `fun a a' h => Subtype.ext ((theta P y hP hb).injective (congrArg Subtype.val h))`. Establish `hsurj : Function.Surjective (thetaChart P y hP hb c hc)`. Introduce and unpack `⟨u, hu⟩`.

Take `⟨x, hx, rfl⟩` from `exists_theta_eq P y hP hb c hc hu`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Set `e` to `RingEquiv.ofBijective (thetaChart P y hP hb c hc) ⟨hinj, hsurj⟩`. Take `⟨p, hp, hev⟩` from `hv`. Use `⟨p.map (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c), hp.map _, (theta P y hP hb).injective ?_⟩` and prove the remaining obligations.

Establish `hcomp : ((theta P y hP hb).comp (algebraMap (Geo.chartRingZ (ι` using `blockIdx n) y c) Ω)).comp (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c) = algebraMap (P.chartRing c) P.FunField := by`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `h1 : e (e.symm x) = x` using `e.apply_symm_apply x`. Conclude with `congrArg Subtype.val h1`. Rewrite using `[Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_map, hcomp]`.

Conclude with `hev`. Introduce `hv`. Conclude with `IsIntegral.map_of_comp_eq (thetaChart P y hP hb c hc) (theta P y hP hb) (RingHom.ext fun _ => rfl) hv`.
-/
theorem isIntegral_theta_iff (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (v : Ω) :
    IsIntegral (P.chartRing c) (theta P y hP hb v) ↔
      IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) v := by
  constructor
  · intro hv
    have hinj : Function.Injective (thetaChart P y hP hb c hc) := fun a a' h =>
      Subtype.ext ((theta P y hP hb).injective (congrArg Subtype.val h))
    have hsurj : Function.Surjective (thetaChart P y hP hb c hc) := by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx, rfl⟩ := exists_theta_eq P y hP hb c hc hu
      exact ⟨⟨x, hx⟩, rfl⟩
    let e := RingEquiv.ofBijective (thetaChart P y hP hb c hc) ⟨hinj, hsurj⟩
    obtain ⟨p, hp, hev⟩ := hv
    refine ⟨p.map (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c), hp.map _,
      (theta P y hP hb).injective ?_⟩
    have hcomp : ((theta P y hP hb).comp (algebraMap (Geo.chartRingZ (ι := blockIdx n) y c) Ω)).comp
        (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c) =
        algebraMap (P.chartRing c) P.FunField := by
      refine RingHom.ext fun x => ?_
      have h1 : e (e.symm x) = x := e.apply_symm_apply x
      exact congrArg Subtype.val h1
    rw [Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_map, hcomp]
    exact hev
  · intro hv
    exact IsIntegral.map_of_comp_eq (thetaChart P y hP hb c hc) (theta P y hP hb)
      (RingHom.ext fun _ => rfl) hv

def readElt (c₀ : (k : ι) → Fin (n k + 1)) (b : ι → ℤ) (s : Ω) : P.FunField :=
  theta P y hP hb (s * ∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * P.chartPow c₀ b

/- English proof (translation)
Introduce `g q δg δq hg hq hd`. Establish `hG : (fun k => (δg k : ℤ)) = b + fun k => (δq k : ℤ)`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.add_apply, hd k, add_comm]`. Establish `hY : (∏ k, y ⟨k, c₀ k⟩ ^ (-(δg k : ℤ))) = (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ))`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc₀ k)]`. Use `congr 1`. Rewrite using `[hd k]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hY0 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ)) ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k)) (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k))`. Rewrite using `[mkF_eq_theta P y hP hb c₀ hc₀ hg, mkF_eq_theta P y hP hb c₀ hc₀ hq, hG, chartPow_add P y hP c₀ hc₀, readElt, show ∀ u v w z : P.FunField, u * w * (v * z) = (u * v) * (w * z) from fun u v w z => by ring, ← map_mul, mul_left_inj' (mul_ne_zero (chartPow_ne_zero P y hP c₀ hc₀ _) (ch …`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Introduce `e`. Apply `mul_right_cancel₀ hY0` to reduce the goal to its premises. Take the linear combination `e`.
-/
theorem reads_readElt (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    P.Reads y b s (readElt P y hP hb c₀ b s) := by
  intro g q δg δq hg hq hd
  have hG : (fun k => (δg k : ℤ)) = b + fun k => (δq k : ℤ) := by
    funext k
    rw [Pi.add_apply, hd k, add_comm]
  have hY : (∏ k, y ⟨k, c₀ k⟩ ^ (-(δg k : ℤ))) =
      (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc₀ k)]
    congr 1
    rw [hd k]
    ring
  have hY0 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ)) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k))
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k))
  rw [mkF_eq_theta P y hP hb c₀ hc₀ hg, mkF_eq_theta P y hP hb c₀ hc₀ hq, hG,
    chartPow_add P y hP c₀ hc₀, readElt,
    show ∀ u v w z : P.FunField, u * w * (v * z) = (u * v) * (w * z) from fun u v w z => by ring,
    ← map_mul, mul_left_inj' (mul_ne_zero (chartPow_ne_zero P y hP c₀ hc₀ _)
      (chartPow_ne_zero P y hP c₀ hc₀ _)), (theta P y hP hb).injective.eq_iff, hY]
  constructor
  · intro e
    rw [e]
    ring
  · intro e
    apply mul_right_cancel₀ hY0
    linear_combination e

/- English proof (translation)
Rewrite using `[readElt, mul_div_assoc, ← theta_chartRatio P y hP hb c₀ c hc b, ← map_mul]`. Use `congr 1`. Establish `h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ b k = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hc₀ k))]`.

Take the linear combination `(s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) * h1`.
-/
theorem readElt_div (c₀ c : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    readElt P y hP hb c₀ b s / P.chartPow c b = theta P y hP hb (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) := by
  rw [readElt, mul_div_assoc, ← theta_chartRatio P y hP hb c₀ c hc b, ← map_mul]
  congr 1
  have h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hc₀ k))]
  linear_combination (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) * h1

/- English proof (translation)
Take `⟨f, q, δf, δq, hf, hq, hd, hq0, he⟩` from `exists_reads_rep y hb c₀ hc₀ b s`. Establish `hmk` using `(reads_readElt P y hP hb c₀ hc₀ b s f q δf δq hf hq hd).mp he`. Establish `hQ : P.mkF q ≠ 0` using `fun h => hq0 ((mkF_eq_zero_iff' P y hP hq).mp h)`. Use `⟨f, q, δf, δq, hf, hq, fun k => by linarith [hd k], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hP, mem_mCoordIdeal_iff y hq]`.

Conclude with `hq0`. Rewrite using `[hmk, mul_div_cancel_right₀ _ hQ]`.
-/
theorem isOfDegree_readElt (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ)
    (s : Ω) : P.IsOfDegree b (readElt P y hP hb c₀ b s) := by
  obtain ⟨f, q, δf, δq, hf, hq, hd, hq0, he⟩ := exists_reads_rep y hb c₀ hc₀ b s
  have hmk := (reads_readElt P y hP hb c₀ hc₀ b s f q δf δq hf hq hd).mp he
  have hQ : P.mkF q ≠ 0 := fun h => hq0 ((mkF_eq_zero_iff' P y hP hq).mp h)
  refine ⟨f, q, δf, δq, hf, hq, fun k => by linarith [hd k], ?_, ?_⟩
  · rw [hP, mem_mCoordIdeal_iff y hq]
    exact hq0
  · rw [hmk, mul_div_cancel_right₀ _ hQ]

end ChartLatNm

open ChartLatNm in

/- English proof (translation)
Introduce `ι _ _ n Ω _ y P a τ s hP hb`. Take `⟨c₀, hc₀⟩` from `P.exists_chart`. Establish `hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0` using `(isLive_iff' P y hP c₀).mp hc₀`. Establish `hab : ∀ k, -((τ : ℤ) * a k) = -((τ • a) k)` using `fun k => by simp`. Establish `hmem : s ∈ Geo.chartLatNm (ι` using `blockIdx n) y a τ ↔ ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ • a) k))) := by`.

Express the relevant statement in the definitionally equal form `(∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ integralClosure (Geo.chartRingZ (ι := blockIdx n) y c) Ω) ↔ _`. Simplify using `only [hab, mem_integralClosure_iff]`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`.

Use `⟨readElt P y hP hb c₀ (τ • a) s, ⟨isOfDegree_readElt P y hP hb c₀ hy₀ _ s, fun c hc => ?_⟩, reads_readElt P y hP hb c₀ hy₀ _ s⟩` and prove the remaining obligations. Establish `hyc` using `(isLive_iff' P y hP c).mp hc`. Rewrite using `[readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff, isIntegral_theta_iff P y hP hb c hyc]`. Conclude with `hs c hyc`. Introduce and unpack `⟨t, ⟨hdeg, hint⟩, hR⟩ c hyc`.

Establish `hc` using `(isLive_iff' P y hP c).mpr hyc`. Take `⟨f, q, δf, δq, hf, hq, hd, hqP, rfl⟩` from `hdeg`. Establish `hQ : P.mkF q ≠ 0` using `fun h => hqP ((P.mkF_eq_zero_iff q).mp h)`. Establish `hd' : ∀ k, (δf k : ℤ) = δq k + (τ • a) k` using `fun k => by linarith [hd k]`. Establish `he` using `(hR f q δf δq hf hq hd').mpr (div_mul_cancel₀ _ hQ).symm`.

Establish `hmk` using `(reads_readElt P y hP hb c₀ hy₀ (τ • a) s f q δf δq hf hq hd').mp he`. Establish `ht : P.mkF f / P.mkF q = readElt P y hP hb c₀ (τ • a) s`. Rewrite using `[hmk, mul_div_cancel_right₀ _ hQ]`. Establish `hi` using `hint c hc`. Rewrite `hi` using `[ht, readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff, isIntegral_theta_iff P y hP hb c hyc]`.

Conclude with `hi`.
-/
theorem ChartLatNmSection.proof : ChartLatNmSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP hb
  obtain ⟨c₀, hc₀⟩ := P.exists_chart
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := (isLive_iff' P y hP c₀).mp hc₀
  have hab : ∀ k, -((τ : ℤ) * a k) = -((τ • a) k) := fun k => by simp
  have hmem : s ∈ Geo.chartLatNm (ι := blockIdx n) y a τ ↔
      ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) →
        IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ • a) k))) := by
    change (∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ integralClosure (Geo.chartRingZ (ι := blockIdx n) y c) Ω) ↔ _
    simp only [hab, mem_integralClosure_iff]
  rw [hmem]
  constructor
  · intro hs
    refine ⟨readElt P y hP hb c₀ (τ • a) s,
      ⟨isOfDegree_readElt P y hP hb c₀ hy₀ _ s, fun c hc => ?_⟩, reads_readElt P y hP hb c₀ hy₀ _ s⟩
    have hyc := (isLive_iff' P y hP c).mp hc
    rw [readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff, isIntegral_theta_iff P y hP hb c hyc]
    exact hs c hyc
  · rintro ⟨t, ⟨hdeg, hint⟩, hR⟩ c hyc
    have hc := (isLive_iff' P y hP c).mpr hyc
    obtain ⟨f, q, δf, δq, hf, hq, hd, hqP, rfl⟩ := hdeg
    have hQ : P.mkF q ≠ 0 := fun h => hqP ((P.mkF_eq_zero_iff q).mp h)
    have hd' : ∀ k, (δf k : ℤ) = δq k + (τ • a) k := fun k => by linarith [hd k]
    have he := (hR f q δf δq hf hq hd').mpr (div_mul_cancel₀ _ hQ).symm
    have hmk := (reads_readElt P y hP hb c₀ hy₀ (τ • a) s f q δf δq hf hq hd').mp he
    have ht : P.mkF f / P.mkF q = readElt P y hP hb c₀ (τ • a) s := by
      rw [hmk, mul_div_cancel_right₀ _ hQ]
    have hi := hint c hc
    rw [ht, readElt_div P y hP hb c₀ c hy₀ hyc, mem_integralClosure_iff,
      isIntegral_theta_iff P y hP hb c hyc] at hi
    exact hi

end

end GroundTheory.Heights₂.Heights
