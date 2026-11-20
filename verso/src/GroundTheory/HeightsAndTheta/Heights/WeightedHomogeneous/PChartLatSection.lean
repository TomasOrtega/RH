import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hg` using `(geoMultiHomog_iff f δ).mpr hf`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hdeg` using `hg m hm`. Simplify using `only [Geo.mConeMap, aeval_monomial, map_mul]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Establish `hX : (∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p) = ∏ k, (X k : MvPolynomial ι Ω) ^ δ k`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hdeg k]`. Rewrite using `[hX, MvPolynomial.algebraMap_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_form (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
  have hg := (geoMultiHomog_iff f δ).mpr hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [Geo.mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p) = ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_form y hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hM : (∏ k, (X k : MvPolynomial ι Ω) ^ δ k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)`. Conclude with `C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)`.

Introduce `h`. Rewrite using `[h, C_0, zero_mul]`.
-/
theorem form_mem_iff (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_form y hf]
  constructor
  · intro h
    have hM : (∏ k, (X k : MvPolynomial ι Ω) ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, C_0, zero_mul]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `h1 : (aeval (fun _ : ι => (1 : Ω))).toRingHom.comp (Geo.mConeMap (ι` using `blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by`. Use `MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [Geo.mConeMap])` and prove the remaining obligations. Establish `h2` using `congrArg (fun φ : _ →+* _ => φ f) h1`. Establish `h3 : Geo.mConeMap (ι` using `blockIdx n) y f = 0 := RingHom.mem_ker.mp hf`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2`.

Rewrite using `[← h2]`.
-/
theorem aeval_eq_zero_of_mem (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) : aeval y f = 0 := by
  have h1 : (aeval (fun _ : ι => (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ => φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2]

omit [DecidableEq ι] in

/- English proof (translation)
Simplify using `[chartMonomial, map_prod]`.
-/
theorem aeval_chartMonomial (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMonomial, map_prod]

/- English proof (translation)
Rewrite using `[hP, form_mem_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) p), aeval_X]`.
-/
theorem coord_notMem_iff (y : Coord n → Ω) {P : ArithVariety n}
    (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (p : Coord n) :
    (X p : MvPolynomial (Coord n) ℤ) ∉ P.ideal ↔ y p ≠ 0 := by
  rw [hP, form_mem_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) p), aeval_X]

/- English proof (translation)
Establish `hpow : ∀ δ₁ δ₂ : ι → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k` using `fun δ₁ δ₂ => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Rewrite `hx` using `[Geo.chartRingZ]`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Use `⟨coordDeg n p, X p, isWeightedHomogeneous_X ℤ _ p, ?_⟩` and prove the remaining obligations. Establish `h1 : ∏ k, y ⟨k, c k⟩ ^ coordDeg n p k = y ⟨p.1, c p.1⟩`. Rewrite using `[Finset.prod_eq_single p.1 (fun k _ hk => by simp [coordDeg, hk]) (fun h => absurd (Finset.mem_univ _) h)]`.

Simplify using `[coordDeg]`. Rewrite using `[aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]`. Consider the case `algebraMap r`. Conclude with `⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨δ₁, e₁, h₁, v₁⟩` from `hx`. Take `⟨δ₂, e₂, h₂, v₂⟩` from `hz`. Use `⟨δ₁ + δ₂, e₁ * chartMonomial c δ₂ + e₂ * chartMonomial c δ₁, (h₁.mul (isWeightedHomogeneous_chartMonomial c δ₂)).add ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm δ₁]`. Conclude with `h₂.mul (isWeightedHomogeneous_chartMonomial c δ₁)`.

Rewrite using `[map_add, map_mul, map_mul, v₁, v₂, aeval_chartMonomial, aeval_chartMonomial, hpow]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x z _ _ hx hz`. Take `⟨δ₁, e₁, h₁, v₁⟩` from `hx`. Take `⟨δ₂, e₂, h₂, v₂⟩` from `hz`.

Use `⟨δ₁ + δ₂, e₁ * e₂, h₁.mul h₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, v₁, v₂, hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form_of_mem_chartRingZ (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ (δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  have hpow : ∀ δ₁ δ₂ : ι → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [Geo.chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨coordDeg n p, X p, isWeightedHomogeneous_X ℤ _ p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ coordDeg n p k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [coordDeg, hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [coordDeg]
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMonomial c δ₂ + e₂ * chartMonomial c δ₁,
      (h₁.mul (isWeightedHomogeneous_chartMonomial c δ₂)).add ?_, ?_⟩
    · rw [add_comm δ₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMonomial, aeval_chartMonomial, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, h₁.mul h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

/- English proof (translation)
Establish `hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ Geo.chartRingZ (ι` using `blockIdx n) y c := hs c hc`. Take `⟨δ', e', he', hv'⟩` from `exists_form_of_mem_chartRingZ y c hc hx`. Use `set ex : ι → ℕ := fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat with hex`. Establish `hexk : ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs` using `fun k => by`. Rewrite using `[hex]`.

Conclude with `Int.toNat_of_nonneg (by omega)`. Use `⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * chartMonomial c ex, he'.mul (isWeightedHomogeneous_chartMonomial c ex), fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_add, hexk k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hv', aeval_chartMonomial, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h0` using `hc k`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_chartForm (y : Coord n → Ω) (a : ι → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ Geo.chartLat (ι := blockIdx n) y a τ) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      (∀ k, (δ k : ℤ) = (τ • a) k + d k) ∧ aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ Geo.chartRingZ (ι := blockIdx n) y c := hs c hc
  obtain ⟨δ', e', he', hv'⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : ι → ℕ := fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * chartMonomial c ex,
    he'.mul (isWeightedHomogeneous_chartMonomial c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv', aeval_chartMonomial, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

end ChartLatSection

open ChartLatSection in

/- English proof (translation)
Introduce `ι _ _ n Ω _ y P a τ s hP`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Take `⟨c₀, hc₀⟩` from `P.exists_chart`. Establish `hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0` using `fun k => (coord_notMem_iff y hP _).mp (hc₀ k)`.

Take `⟨d₀, δ₀, e₀, he₀, hδ₀, hv₀⟩` from `exists_chartForm y a τ hs c₀ hy₀`. Establish `hm₀ : ∏ k, y ⟨k, c₀ k⟩ ^ d₀ k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy₀ k)`. Establish `hden : chartMonomial c₀ d₀ ∉ P.ideal`. Rewrite using `[hP, form_mem_iff y (isWeightedHomogeneous_chartMonomial c₀ d₀), aeval_chartMonomial]`. Conclude with `hm₀`.

Use `⟨⟨e₀, chartMonomial c₀ d₀, δ₀, d₀, he₀, isWeightedHomogeneous_chartMonomial c₀ d₀, fun k => by rw [hδ₀ k]; ring, hden, fun c hc => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (coord_notMem_iff y hP _).mp (hc k)`. Take `⟨d, δ, e, he, hδ, hv⟩` from `exists_chartForm y a τ hs c hyc`. Use `⟨d, e, ⟨δ, he, hδ⟩, ?_⟩` and prove the remaining obligations. Establish `hdeg : d₀ + δ = δ₀ + d`.

Use function extensionality and compare the values at `k`. Establish `h1` using `hδ k`. Establish `h2` using `hδ₀ k`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.

Establish `hhom : IsWeightedHomogeneous (coordDeg n) (chartMonomial c₀ d₀ * e - e₀ * chartMonomial c d) (d₀ + δ)`. Use `((isWeightedHomogeneous_chartMonomial c₀ d₀).mul he).sub ?_` and prove the remaining obligations. Rewrite using `[hdeg]`. Conclude with `he₀.mul (isWeightedHomogeneous_chartMonomial c d)`. Rewrite using `[hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv, hv₀, aeval_chartMonomial, aeval_chartMonomial]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `g h δg δh hg hh hd`. Establish `hmk : P.mkF (chartMonomial c₀ d₀) ≠ 0`. Rewrite using `[Ne, P.mkF_eq_zero_iff]`. Conclude with `hden`.

Establish `hdeg : δg + d₀ = δ₀ + δh`. Use function extensionality and compare the values at `k`. Establish `h1` using `hd k`. Establish `h2` using `hδ₀ k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h1 h2 ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c₀ d₀ - e₀ * h) (δg + d₀)`. Use `(hg.mul (isWeightedHomogeneous_chartMonomial c₀ d₀)).sub ?_` and prove the remaining obligations. Rewrite using `[hdeg]`. Conclude with `he₀.mul hh`.

Establish `key : P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h ↔ g * chartMonomial c₀ d₀ - e₀ * h ∈ P.ideal`. Rewrite using `[← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hmk]`. Use `show _ ↔ P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h`. Rewrite using `[key, hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv₀, aeval_chartMonomial, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h1`. Apply `mul_right_cancel₀ hm₀` to reduce the goal to its premises.

Take the linear combination `h1`. Introduce and unpack `⟨t, ht⟩`. Establish `hyP : ∀ f ∈ P.ideal, aeval y f = 0` using `fun f hf => aeval_eq_zero_of_mem y (hP ▸ hf)`. Establish `hG : aeval y t.den ≠ 0`. Introduce `h0`.

Conclude with `t.den_not_mem (by rw [hP, form_mem_iff y t.den_isHomogeneous]; exact h0)`. Establish `hmk : P.mkF t.den ≠ 0`. Rewrite using `[Ne, P.mkF_eq_zero_iff]`. Conclude with `t.den_not_mem`. Establish `hread : aeval y t.num = s * aeval y t.den`.

Use `(ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous (fun k => by have := t.deg_eq k; linarith)).mpr ?_` and prove the remaining obligations. Use `show P.mkF t.num = P.mkF t.num / P.mkF t.den * P.mkF t.den`. Rewrite using `[div_mul_cancel₀ _ hmk]`. Establish `hs : s = aeval y t.num / aeval y t.den`. Rewrite using `[hread, mul_div_assoc, div_self hG, mul_one]`.

Establish `hmem` using `t.value_mem_chartLat y hyP hG`. Rewrite `hmem` using `[← hs]`. Introduce `c hc`. Establish `h` using `hmem c hc`. Establish `he : ∀ k, -(((1 : ℕ) : ℤ) * (τ • a) k) = -((τ : ℤ) * a k)` using `fun k => by`.

Simplify using the standard rewrite rules. Simplify using `only [he] at h`. Conclude with `h`.
-/
theorem ChartLatSection.proof : ChartLatSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP
  constructor
  · intro hs
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc₀ k)
    obtain ⟨d₀, δ₀, e₀, he₀, hδ₀, hv₀⟩ := exists_chartForm y a τ hs c₀ hy₀
    have hm₀ : ∏ k, y ⟨k, c₀ k⟩ ^ d₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy₀ k)
    have hden : chartMonomial c₀ d₀ ∉ P.ideal := by
      rw [hP, form_mem_iff y (isWeightedHomogeneous_chartMonomial c₀ d₀), aeval_chartMonomial]
      exact hm₀
    refine ⟨⟨e₀, chartMonomial c₀ d₀, δ₀, d₀, he₀, isWeightedHomogeneous_chartMonomial c₀ d₀,
      fun k => by rw [hδ₀ k]; ring, hden, fun c hc => ?_⟩, ?_⟩
    · have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc k)
      obtain ⟨d, δ, e, he, hδ, hv⟩ := exists_chartForm y a τ hs c hyc
      refine ⟨d, e, ⟨δ, he, hδ⟩, ?_⟩
      have hdeg : d₀ + δ = δ₀ + d := by
        funext k
        have h1 := hδ k
        have h2 := hδ₀ k
        simp only [Pi.add_apply]
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n)
          (chartMonomial c₀ d₀ * e - e₀ * chartMonomial c d) (d₀ + δ) := by
        refine ((isWeightedHomogeneous_chartMonomial c₀ d₀).mul he).sub ?_
        rw [hdeg]
        exact he₀.mul (isWeightedHomogeneous_chartMonomial c d)
      rw [hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv, hv₀, aeval_chartMonomial,
        aeval_chartMonomial]
      ring
    · intro g h δg δh hg hh hd
      have hmk : P.mkF (chartMonomial c₀ d₀) ≠ 0 := by
        rw [Ne, P.mkF_eq_zero_iff]
        exact hden
      have hdeg : δg + d₀ = δ₀ + δh := by
        funext k
        have h1 := hd k
        have h2 := hδ₀ k
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h1 h2 ⊢
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c₀ d₀ - e₀ * h) (δg + d₀) := by
        refine (hg.mul (isWeightedHomogeneous_chartMonomial c₀ d₀)).sub ?_
        rw [hdeg]
        exact he₀.mul hh
      have key : P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h ↔
          g * chartMonomial c₀ d₀ - e₀ * h ∈ P.ideal := by
        rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, sub_eq_zero, div_mul_eq_mul_div,
          eq_div_iff hmk]
      show _ ↔ P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h
      rw [key, hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv₀, aeval_chartMonomial,
        sub_eq_zero]
      constructor
      · intro h1
        rw [h1]
        ring
      · intro h1
        apply mul_right_cancel₀ hm₀
        linear_combination h1
  · rintro ⟨t, ht⟩
    have hyP : ∀ f ∈ P.ideal, aeval y f = 0 := fun f hf => aeval_eq_zero_of_mem y (hP ▸ hf)
    have hG : aeval y t.den ≠ 0 := by
      intro h0
      exact t.den_not_mem (by rw [hP, form_mem_iff y t.den_isHomogeneous]; exact h0)
    have hmk : P.mkF t.den ≠ 0 := by
      rw [Ne, P.mkF_eq_zero_iff]
      exact t.den_not_mem
    have hread : aeval y t.num = s * aeval y t.den := by
      refine (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
        (fun k => by have := t.deg_eq k; linarith)).mpr ?_
      show P.mkF t.num = P.mkF t.num / P.mkF t.den * P.mkF t.den
      rw [div_mul_cancel₀ _ hmk]
    have hs : s = aeval y t.num / aeval y t.den := by
      rw [hread, mul_div_assoc, div_self hG, mul_one]
    have hmem := t.value_mem_chartLat y hyP hG
    rw [← hs] at hmem
    intro c hc
    have h := hmem c hc
    have he : ∀ k, -(((1 : ℕ) : ℤ) * (τ • a) k) = -((τ : ℤ) * a k) := fun k => by
      simp
    simp only [he] at h
    exact h

end

end GroundTheory.Heights₂.Heights
