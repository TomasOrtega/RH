import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.HostModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section General

/- English proof (translation)
Establish `h0 : ∀ x, σ x = x → D x = 0` using `fun x hx => by`. Take `⟨a, rfl⟩` from `hfix x hx`. Conclude with `D.map_algebraMap a`. Establish `h1 : ∀ x, D (σ x) = -D x` using `fun x => by`. Establish `h` using `h0 (x + σ x) (by rw [map_add, hσ, add_comm])`.

Rewrite `h` using `[map_add]`. Conclude with `eq_neg_of_add_eq_zero_right h`. Establish `h2 : ∀ x, (x - σ x) • D x = 0` using `fun x => by`. Establish `h` using `h0 (σ x * x) (by rw [map_mul, hσ, mul_comm])`. Rewrite `h` using `[D.leibniz, h1, smul_neg, ← sub_eq_add_neg, ← sub_smul]`.

Rewrite using `[← neg_sub, neg_smul, h, neg_zero]`. Establish `h3 : (w - σ w) • D b + (b - σ b) • D w = 0`. Establish `h` using `h2 (w + b)`. Establish `e : w + b - σ (w + b) = (w - σ w) + (b - σ b)` using `by rw [map_add]; ring`. Rewrite `h` using `[e, map_add, add_smul, smul_add, smul_add, h2, h2, zero_add, add_zero]`.

Conclude with `h`. Establish `h4` using `congrArg (fun m => (w - σ w) • m) h3`. Simplify using `only [smul_add, smul_zero] at h4`. Rewrite `h4` using `[smul_comm (w - σ w) (b - σ b), h2, smul_zero, add_zero, ← mul_smul, ← sq]`. Conclude with `h4`.
-/
theorem sq_sub_smul_derivation_eq_zero {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] [Module B M] (D : Derivation A B M) (σ : B →+* B) (hσ : ∀ b, σ (σ b) = b)
    (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w b : B) : (w - σ w) ^ 2 • D b = 0 := by
  have h0 : ∀ x, σ x = x → D x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := hfix x hx
    exact D.map_algebraMap a
  have h1 : ∀ x, D (σ x) = -D x := fun x => by
    have h := h0 (x + σ x) (by rw [map_add, hσ, add_comm])
    rw [map_add] at h
    exact eq_neg_of_add_eq_zero_right h
  have h2 : ∀ x, (x - σ x) • D x = 0 := fun x => by
    have h := h0 (σ x * x) (by rw [map_mul, hσ, mul_comm])
    rw [D.leibniz, h1, smul_neg, ← sub_eq_add_neg, ← sub_smul] at h
    rw [← neg_sub, neg_smul, h, neg_zero]
  have h3 : (w - σ w) • D b + (b - σ b) • D w = 0 := by
    have h := h2 (w + b)
    have e : w + b - σ (w + b) = (w - σ w) + (b - σ b) := by rw [map_add]; ring
    rw [e, map_add, add_smul, smul_add, smul_add, h2, h2, zero_add, add_zero] at h
    exact h
  have h4 := congrArg (fun m => (w - σ w) • m) h3
  simp only [smul_add, smul_zero] at h4
  rw [smul_comm (w - σ w) (b - σ b), h2, smul_zero, add_zero, ← mul_smul, ← sq] at h4
  exact h4

/- English proof (translation)
Establish `hD : ∀ b, KaehlerDifferential.D A B b = 0` using `fun b => by`. Take `⟨u, v, huv⟩ : IsCoprime ((w₁ - σ w₁) ^ 2) ((w₂ - σ w₂) ^ 2)` from `h.pow`. Rewrite using `[← one_smul B (KaehlerDifferential.D A B b), ← huv, add_smul, mul_smul, mul_smul, sq_sub_smul_derivation_eq_zero _ σ hσ hfix, sq_sub_smul_derivation_eq_zero _ σ hσ hfix, smul_zero, smul_zero, add_zero]`. Establish `hbot : (⊤ : Submodule B (Ω[B⁄A])) = ⊥`. Rewrite using `[← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]`.

Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `hD b`. Use `⟨⟨fun x y => ?_⟩⟩` and prove the remaining obligations. Establish `hz : ∀ z : Ω[B⁄A], z = 0` using `fun z => by`. Rewrite using `[← Submodule.mem_bot B, ← hbot]`.

Discharge the goal by the elementary cases of `trivial`. Rewrite using `[hz x, hz y]`.
-/
theorem formallyUnramified_of_isCoprime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →+* B)
    (hσ : ∀ b, σ (σ b) = b) (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w₁ w₂ : B)
    (h : IsCoprime (w₁ - σ w₁) (w₂ - σ w₂)) : Algebra.FormallyUnramified A B := by
  have hD : ∀ b, KaehlerDifferential.D A B b = 0 := fun b => by
    obtain ⟨u, v, huv⟩ : IsCoprime ((w₁ - σ w₁) ^ 2) ((w₂ - σ w₂) ^ 2) := h.pow
    rw [← one_smul B (KaehlerDifferential.D A B b), ← huv, add_smul, mul_smul, mul_smul,
      sq_sub_smul_derivation_eq_zero _ σ hσ hfix, sq_sub_smul_derivation_eq_zero _ σ hσ hfix, smul_zero, smul_zero,
      add_zero]
  have hbot : (⊤ : Submodule B (Ω[B⁄A])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨b, rfl⟩
    exact hD b
  refine ⟨⟨fun x y => ?_⟩⟩
  have hz : ∀ z : Ω[B⁄A], z = 0 := fun z => by
    rw [← Submodule.mem_bot B, ← hbot]
    trivial
  rw [hz x, hz y]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `{ formallyUnramified := formallyUnramified_of_isCoprime (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) (fun b => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (b : E))) (fun b hb => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E b).1 hb) w₁ w₂ h finiteType := …`.
-/
theorem unramified_of_isCoprime (w₁ w₂ : 𝓞 E)
    (h : IsCoprime (w₁ - IsCMField.ringOfIntegersComplexConj E w₁) (w₂ - IsCMField.ringOfIntegersComplexConj E w₂)) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  { formallyUnramified := formallyUnramified_of_isCoprime (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
      (fun b => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (b : E)))
      (fun b hb => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E b).1 hb) w₁ w₂ h
    finiteType := inferInstance }

/- English proof (translation)
Set `φ : E →+* ℂ` to `Classical.choice inferInstance`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj, map_neg]`. Establish `h : φ x ^ 2 = -(n : ℂ)` using `by rw [← map_pow, hx, map_neg, map_natCast]`. Establish `hre` using `congrArg Complex.re h`.

Establish `him` using `congrArg Complex.im h`. Simplify using `only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `h0 : (φ x).re = 0`. Assume the negation of the conclusion as `hne`.

Establish `hi : (φ x).im = 0`. Establish `: (φ x).re * (φ x).im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hre` using `[hi]`. Use `mul_self_pos.2 hne` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem complexConj_eq_neg_of_sq_eq_neg {x : E} {n : ℕ} (hx : x ^ 2 = -(n : E)) : IsCMField.complexConj E x = -x := by
  let φ : E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h : φ x ^ 2 = -(n : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : (φ x).re = 0 := by
    by_contra hne
    have hi : (φ x).im = 0 := by
      have : (φ x).re * (φ x).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [hi] at hre
    have := mul_self_pos.2 hne
    linarith
  apply Complex.ext <;> simp [h0]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `h` using `congrArg (fun y : 𝓞 E => (y : E)) hx`. Simplify using `using h`.
-/
theorem _root_.GlobalTheory.HostModel.coe_sq_eq_neg {x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) : (x : E) ^ 2 = -(n : E) := by
  have h := congrArg (fun y : 𝓞 E => (y : E)) hx
  simpa using h

/- English proof (translation)
Establish `hx' : IsCMField.ringOfIntegersComplexConj E x = -x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h : (x : E) ^ 2 = -(n : E)` using `coe_sq_eq_neg hx`. Conclude with `complexConj_eq_neg_of_sq_eq_neg h`. Establish `h` using `congrArg (IsCMField.ringOfIntegersComplexConj E) hw`.

Rewrite `h` using `[map_mul, map_add, map_one, hx', map_ofNat]`. Apply `mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)` to reduce the goal to its premises. Take the linear combination `hw - h`.
-/
theorem sub_complexConj_eq_of_two_mul {w x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) (hw : 2 * w = 1 + x) :
    w - IsCMField.ringOfIntegersComplexConj E w = x := by
  have hx' : IsCMField.ringOfIntegersComplexConj E x = -x := by
    apply RingOfIntegers.ext
    have h : (x : E) ^ 2 = -(n : E) := coe_sq_eq_neg hx
    exact complexConj_eq_neg_of_sq_eq_neg h
  have h := congrArg (IsCMField.ringOfIntegersComplexConj E) hw
  rw [map_mul, map_add, map_one, hx', map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  linear_combination hw - h

/- English proof (translation)
Apply `unramified_of_isCoprime w₁ w₂` to reduce the goal to its premises. Rewrite using `[sub_complexConj_eq_of_two_mul h₁ hw₁, sub_complexConj_eq_of_two_mul h₂ hw₂, ← IsCoprime.pow_iff (m := 2) (n := 2) two_pos two_pos, h₁, h₂, IsCoprime.neg_neg_iff]`. Conclude with `hmn.cast`.
-/
theorem unramified_of_sqrt {x₁ x₂ w₁ w₂ : 𝓞 E} {m n : ℕ} (hmn : m.Coprime n) (h₁ : x₁ ^ 2 = -(m : 𝓞 E))
    (h₂ : x₂ ^ 2 = -(n : 𝓞 E)) (hw₁ : 2 * w₁ = 1 + x₁) (hw₂ : 2 * w₂ = 1 + x₂) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
  apply unramified_of_isCoprime w₁ w₂
  rw [sub_complexConj_eq_of_two_mul h₁ hw₁, sub_complexConj_eq_of_two_mul h₂ hw₂,
    ← IsCoprime.pow_iff (m := 2) (n := 2) two_pos two_pos, h₁, h₂, IsCoprime.neg_neg_iff]
  exact hmn.cast

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Set `φ : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Use `set w := φ (H.rt : E) with hw`. Establish `hw2 : w ^ 2 = -(H.d : ℂ)`. Rewrite using `[hw, ← map_pow, _root_.GlobalTheory.HostModel.coe_sq_eq_neg H.rt_sq]`. Simplify using the standard rewrite rules.

Establish `hre : w.re = 0`. Establish `h` using `congrArg Complex.re hw2`. Establish `h'` using `congrArg Complex.im hw2`. Simplify using `[pow_two] at h h'`. Assume the negation of the conclusion as `hne`.

Establish `him : w.im = 0`. Establish `h0 : w.re * w.im = 0` using `by linarith`. Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Conclude with `absurd h1 hne`. Conclude with `h1`.

Rewrite `h` using `[him]`. Establish `hd : (0 : ℝ) ≤ H.d` using `Nat.cast_nonneg _`. Establish `hpos : 0 < w.re * w.re` using `mul_self_pos.mpr hne`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hconj : (starRingEnd ℂ) w = -w`.

Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Establish `hfac : (H.rt0 - w) * (H.rt0 + w) = 0`. Take the linear combination `H.sqrt_neg_disc_sq - hw2`. Break down `mul_eq_zero.mp hfac with h | h` into its components or cases. Use `⟨φ, ?_⟩ show w = H.rt0` and prove the remaining obligations.

Take the linear combination `-h`. Use `⟨(starRingEnd ℂ).comp φ, ?_⟩ show (starRingEnd ℂ) w = H.rt0` and prove the remaining obligations. Rewrite using `[hconj]`. Take the linear combination `-h`.
-/
theorem _root_.GlobalTheory.HostModel.exists_embedding_rt_eq (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  set w := φ (H.rt : E) with hw
  have hw2 : w ^ 2 = -(H.d : ℂ) := by
    rw [hw, ← map_pow, _root_.GlobalTheory.HostModel.coe_sq_eq_neg H.rt_sq]
    simp
  have hre : w.re = 0 := by
    have h := congrArg Complex.re hw2
    have h' := congrArg Complex.im hw2
    simp [pow_two] at h h'
    by_contra hne
    have him : w.im = 0 := by
      have h0 : w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hne
      · exact h1
    rw [him] at h
    have hd : (0 : ℝ) ≤ H.d := Nat.cast_nonneg _
    have hpos : 0 < w.re * w.re := mul_self_pos.mpr hne
    linarith
  have hconj : (starRingEnd ℂ) w = -w := by
    apply Complex.ext <;> simp [hre]
  have hfac : (H.rt0 - w) * (H.rt0 + w) = 0 := by
    linear_combination H.sqrt_neg_disc_sq - hw2
  rcases mul_eq_zero.mp hfac with h | h
  · refine ⟨φ, ?_⟩
    show w = H.rt0
    linear_combination -h
  · refine ⟨(starRingEnd ℂ).comp φ, ?_⟩
    show (starRingEnd ℂ) w = H.rt0
    rw [hconj]
    linear_combination -h

end General

abbrev E21 : Type := CyclotomicField 21 ℚ

instance isCyclotomicExtension_cyclotomicField21 : IsCyclotomicExtension {21} ℚ E21 := CyclotomicField.isCyclotomicExtension 21 ℚ

instance isCMField_cyclotomicField21 : IsCMField E21 := IsCyclotomicExtension.Rat.isCMField E21 (S := {21}) ⟨21, rfl, by norm_num⟩

def primitiveRootCyclotomicField21 : 𝓞 E21 := (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger

/- English proof (translation)
The claim follows from `(IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger_isPrimitiveRoot`.
-/
theorem isPrimitiveRoot_primitiveRootCyclotomicField21 : IsPrimitiveRoot primitiveRootCyclotomicField21 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger_isPrimitiveRoot

/- English proof (translation)
Establish `h : IsPrimitiveRoot (primitiveRootCyclotomicField21 ^ 3) 7` using `isPrimitiveRoot_primitiveRootCyclotomicField21.pow (by norm_num) (by norm_num)`. Establish `h2` using `h.geom_sum_eq_zero (by norm_num)`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero] at h2`. Take the linear combination `h2`.
-/
theorem sum_zeta21_pow_multiples_of_three_eq_zero : 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 9 + primitiveRootCyclotomicField21 ^ 12 + primitiveRootCyclotomicField21 ^ 15 + primitiveRootCyclotomicField21 ^ 18 = 0 := by
  have h : IsPrimitiveRoot (primitiveRootCyclotomicField21 ^ 3) 7 := isPrimitiveRoot_primitiveRootCyclotomicField21.pow (by norm_num) (by norm_num)
  have h2 := h.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  linear_combination h2

def halfSqrtNegSeven : 𝓞 E21 := 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 12

def sqrtNegSeven : 𝓞 E21 := 2 * halfSqrtNegSeven - 1

def sqrtNegThree : 𝓞 E21 := 1 + 2 * primitiveRootCyclotomicField21 ^ 7

/- English proof (translation)
Establish `h` using `isPrimitiveRoot_primitiveRootCyclotomicField21.pow_eq_one`. Unfold `halfSqrtNegSeven`. Take the linear combination `2 * sum_zeta21_pow_multiples_of_three_eq_zero + primitiveRootCyclotomicField21 ^ 3 * h`.
-/
theorem halfSqrtNegSeven_quadratic : halfSqrtNegSeven ^ 2 - halfSqrtNegSeven + 2 = 0 := by
  have h := isPrimitiveRoot_primitiveRootCyclotomicField21.pow_eq_one
  unfold halfSqrtNegSeven
  linear_combination 2 * sum_zeta21_pow_multiples_of_three_eq_zero + primitiveRootCyclotomicField21 ^ 3 * h

open NumberField in
/- English proof (translation)
The claim follows from `(IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21).toInteger_isPrimitiveRoot`.
-/
private theorem isPrimitiveRoot_hostModel_primitiveRoot21 :
    IsPrimitiveRoot _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21).toInteger_isPrimitiveRoot

open NumberField in

/- English proof (translation)
Establish `hz` using `isPrimitiveRoot_hostModel_primitiveRoot21`. Establish `hω : IsPrimitiveRoot (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3) 7` using `hz.pow (by norm_num) (by norm_num)`. Establish `h1` using `hω.geom_sum_eq_zero (by norm_num)`. Establish `h2` using `hz.pow_eq_one`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero] at h1`.

Unfold `_root_.GlobalTheory.HostModel.sqrtNegSeven _root_.GlobalTheory.HostModel.halfSqrtNegSeven`. Use `push_cast`. Take the linear combination `8 * h1 + 4 * _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3 * h2`.
-/
theorem _root_.GlobalTheory.HostModel.sqrtNegSeven_sq : _root_.GlobalTheory.HostModel.sqrtNegSeven ^ 2 = -((7 : ℕ) : 𝓞 _root_.GlobalTheory.HostModel.E21) := by
  have hz := isPrimitiveRoot_hostModel_primitiveRoot21
  have hω : IsPrimitiveRoot (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3) 7 := hz.pow (by norm_num) (by norm_num)
  have h1 := hω.geom_sum_eq_zero (by norm_num)
  have h2 := hz.pow_eq_one
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  unfold _root_.GlobalTheory.HostModel.sqrtNegSeven _root_.GlobalTheory.HostModel.halfSqrtNegSeven
  push_cast
  linear_combination 8 * h1 + 4 * _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 3 * h2

open NumberField in
/- English proof (translation)
Establish `hz` using `isPrimitiveRoot_hostModel_primitiveRoot21`. Set `φ : _root_.GlobalTheory.HostModel.E21 →+* ℂ` to `(IsAlgClosed.lift : _root_.GlobalTheory.HostModel.E21 →ₐ[ℚ] ℂ).toRingHom`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show ((IsCMField.ringOfIntegersComplexConj _root_.GlobalTheory.HostModel.E21 _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : 𝓞 _root_.GlobalTheory.HostModel.E21) : _root_.GlobalTheory.HostModel.E21) = ((_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ …`. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj]`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Establish `hw : IsPrimitiveRoot (φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)) 21` using `(hz.map_of_injective RingOfIntegers.coe_injective).map_of_injective φ.injective`. Use `set w := φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)`. Establish `hnorm : w * (starRingEnd ℂ) w = 1`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hw.norm'_eq_one (by norm_num)]`. Evaluate the numerical expressions. Establish `h21 : w * w ^ 20 = 1` using `by rw [← pow_succ']; exact hw.pow_eq_one`. Establish `hw0 : w ≠ 0` using `hw.ne_zero (by norm_num)`. Use `push_cast`.

Rewrite using `[map_pow]`. Conclude with `mul_left_cancel₀ hw0 (hnorm.trans h21.symm)`.
-/
private theorem ringOfIntegersComplexConj_zeta21_eq_pow_twenty :
    IsCMField.ringOfIntegersComplexConj _root_.GlobalTheory.HostModel.E21 _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 =
      _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 20 := by
  have hz := isPrimitiveRoot_hostModel_primitiveRoot21
  let φ : _root_.GlobalTheory.HostModel.E21 →+* ℂ := (IsAlgClosed.lift : _root_.GlobalTheory.HostModel.E21 →ₐ[ℚ] ℂ).toRingHom
  apply RingOfIntegers.coe_injective
  show ((IsCMField.ringOfIntegersComplexConj _root_.GlobalTheory.HostModel.E21 _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 :
      𝓞 _root_.GlobalTheory.HostModel.E21) : _root_.GlobalTheory.HostModel.E21) =
    ((_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 ^ 20 : 𝓞 _root_.GlobalTheory.HostModel.E21) : _root_.GlobalTheory.HostModel.E21)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hw : IsPrimitiveRoot (φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)) 21 :=
    (hz.map_of_injective RingOfIntegers.coe_injective).map_of_injective φ.injective
  set w := φ (_root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21 : _root_.GlobalTheory.HostModel.E21)
  have hnorm : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw.norm'_eq_one (by norm_num)]
    norm_num
  have h21 : w * w ^ 20 = 1 := by rw [← pow_succ']; exact hw.pow_eq_one
  have hw0 : w ≠ 0 := hw.ne_zero (by norm_num)
  push_cast
  rw [map_pow]
  exact mul_left_cancel₀ hw0 (hnorm.trans h21.symm)

open NumberField in
/- English proof (translation)
Establish `hroot` using `hu.isRoot_cyclotomic (by norm_num)`. Rewrite `hroot` using `[← Polynomial.mul_divByMonic_eq_iff_isRoot]`. Establish `hnpp : ∀ {p : ℕ}, Nat.Prime p → ∀ k : ℕ, p ^ k ≠ 21`. Introduce `p hp k hk`. Establish `h3 : 3 ∣ p` using `Nat.prime_three.dvd_of_dvd_pow (hk ▸ (by norm_num : 3 ∣ 21))`.

Establish `h7 : 7 ∣ p` using `(by norm_num : Nat.Prime 7).dvd_of_dvd_pow (hk ▸ (by norm_num : 7 ∣ 21))`. Establish `e3` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3`. Establish `e7` using `(Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) hp).mp h7`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (Polynomial.eval 1) hroot`.

Rewrite `h1` using `[Polynomial.eval_mul, Polynomial.eval_one_cyclotomic_not_prime_pow hnpp]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1`. Conclude with `IsUnit.of_mul_eq_one _ h1`.
-/
private theorem isUnit_one_sub_of_isPrimitiveRoot_twentyOne {R : Type*} [CommRing R] [IsDomain R] {u : R}
    (hu : IsPrimitiveRoot u 21) : IsUnit (1 - u) := by
  have hroot := hu.isRoot_cyclotomic (by norm_num)
  rw [← Polynomial.mul_divByMonic_eq_iff_isRoot] at hroot
  have hnpp : ∀ {p : ℕ}, Nat.Prime p → ∀ k : ℕ, p ^ k ≠ 21 := by
    intro p hp k hk
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (hk ▸ (by norm_num : 3 ∣ 21))
    have h7 : 7 ∣ p := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow (hk ▸ (by norm_num : 7 ∣ 21))
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e7 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) hp).mp h7
    omega
  have h1 := congrArg (Polynomial.eval 1) hroot
  rw [Polynomial.eval_mul, Polynomial.eval_one_cyclotomic_not_prime_pow hnpp] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  exact IsUnit.of_mul_eq_one _ h1

open NumberField in

/- English proof (translation)
Use `set ζ := _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21`. Establish `hz : IsPrimitiveRoot ζ 21` using `isPrimitiveRoot_hostModel_primitiveRoot21`. Establish `hconj` using `ringOfIntegersComplexConj_zeta21_eq_pow_twenty`. Establish `hζ21 : ζ ^ 21 = 1` using `hz.pow_eq_one`. Take `⟨t, ht⟩` from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff _root_.GlobalTheory.HostModel.E21 (ζ + ζ ^ 20)).mp (by`.

Rewrite using `[map_add, map_pow, hconj, ← pow_mul]`. Take the linear combination `(ζ ^ 379 + ζ ^ 358 + ζ ^ 337 + ζ ^ 316 + ζ ^ 295 + ζ ^ 274 + ζ ^ 253 + ζ ^ 232 + ζ ^ 211 + ζ ^ 190 + ζ ^ 169 + ζ ^ 148 + ζ ^ 127 + ζ ^ 106 + ζ ^ 85 + ζ ^ 64 + ζ ^ 43 + ζ ^ 22 + ζ) * hζ21)`. Establish `hunit : IsUnit (ζ - ζ ^ 20)`. Establish `h2 : IsPrimitiveRoot (ζ ^ 2) 21` using `hz.pow_of_coprime 2 (by norm_num)`. Establish `hu` using `(isUnit_one_sub_of_isPrimitiveRoot_twentyOne h2).neg.mul (IsUnit.pow 20 (hz.isUnit (by norm_num)))`.

Use `hu using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-1 : 𝓞 _root_.GlobalTheory.HostModel.E21) * ζ * hζ21`. Set `D` to `KaehlerDifferential.D (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21)`. Establish `hDζ : D ζ = 0`. Establish `hDt : D (ζ + ζ ^ 20) = 0`.

Rewrite using `[← ht]`. Conclude with `D.map_algebraMap t`. Establish `hprod : D (ζ * ζ ^ 20) = 0`. Rewrite using `[← pow_succ', hζ21]`. Conclude with `D.map_one_eq_zero`.

Rewrite `hprod` using `[Derivation.leibniz]`. Rewrite `hDt` using `[map_add]`. Establish `key : (ζ - ζ ^ 20) • D ζ = 0`. Establish `e : (ζ - ζ ^ 20) • D ζ = ζ • (D ζ + D (ζ ^ 20)) - (ζ • D (ζ ^ 20) + ζ ^ 20 • D ζ)`. Rewrite using `[sub_smul, smul_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, hDt, hprod, smul_zero, sub_zero]`. Conclude with `(hunit.smul_left_cancel).mp (key.trans (smul_zero _).symm)`. Establish `hall : ∀ x, D x = 0`. Introduce `x`.

Establish `hx : x ∈ Algebra.adjoin ℤ {ζ}`. Establish `htop : Algebra.adjoin ℤ {ζ} = ⊤` using `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21)`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Use `Derivation.eqOn_adjoin (D1 := D.restrictScalars ℤ) (D2 := 0) (s := {ζ}) (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hDζ) hx` as an intermediate fact.

Simplify using `using this`. Establish `hsub : Subsingleton (Ω[𝓞 _root_.GlobalTheory.HostModel.E21⁄𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)])`. Establish `htop` using `KaehlerDifferential.span_range_derivation (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21)`. Establish `hbot : Submodule.span (𝓞 _root_.GlobalTheory.HostModel.E21) (Set.range D) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hall x`. Rewrite `htop` using `[hbot]`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Establish `ha : a ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _)` using `htop ▸ Submodule.mem_top`.

Establish `hb : b ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _)` using `htop ▸ Submodule.mem_top`. Rewrite `ha`, `hb` using `[Submodule.mem_bot]`. Rewrite using `[ha, hb]`. Use `haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := ⟨hsub⟩`. Use `haveI : Algebra.FiniteType (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _`.

Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem _root_.GlobalTheory.HostModel.unramified_E21_over_maximalRealSubfield : Algebra.Unramified (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := by
  set ζ := _root_.GlobalTheory.HostModel.primitiveRootCyclotomicField21
  have hz : IsPrimitiveRoot ζ 21 := isPrimitiveRoot_hostModel_primitiveRoot21
  have hconj := ringOfIntegersComplexConj_zeta21_eq_pow_twenty
  have hζ21 : ζ ^ 21 = 1 := hz.pow_eq_one
  obtain ⟨t, ht⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff _root_.GlobalTheory.HostModel.E21 (ζ + ζ ^ 20)).mp (by
    rw [map_add, map_pow, hconj, ← pow_mul]
    linear_combination (ζ ^ 379 + ζ ^ 358 + ζ ^ 337 + ζ ^ 316 + ζ ^ 295 + ζ ^ 274 + ζ ^ 253 +
      ζ ^ 232 + ζ ^ 211 + ζ ^ 190 + ζ ^ 169 + ζ ^ 148 + ζ ^ 127 + ζ ^ 106 + ζ ^ 85 + ζ ^ 64 +
      ζ ^ 43 + ζ ^ 22 + ζ) * hζ21)
  have hunit : IsUnit (ζ - ζ ^ 20) := by
    have h2 : IsPrimitiveRoot (ζ ^ 2) 21 := hz.pow_of_coprime 2 (by norm_num)
    have hu := (isUnit_one_sub_of_isPrimitiveRoot_twentyOne h2).neg.mul (IsUnit.pow 20 (hz.isUnit (by norm_num)))
    convert hu using 1
    linear_combination (-1 : 𝓞 _root_.GlobalTheory.HostModel.E21) * ζ * hζ21
  let D := KaehlerDifferential.D (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21)
  have hDζ : D ζ = 0 := by
    have hDt : D (ζ + ζ ^ 20) = 0 := by
      rw [← ht]
      exact D.map_algebraMap t
    have hprod : D (ζ * ζ ^ 20) = 0 := by
      rw [← pow_succ', hζ21]
      exact D.map_one_eq_zero
    rw [Derivation.leibniz] at hprod
    rw [map_add] at hDt
    have key : (ζ - ζ ^ 20) • D ζ = 0 := by
      have e : (ζ - ζ ^ 20) • D ζ = ζ • (D ζ + D (ζ ^ 20)) - (ζ • D (ζ ^ 20) + ζ ^ 20 • D ζ) := by
        rw [sub_smul, smul_add]
        abel
      rw [e, hDt, hprod, smul_zero, sub_zero]
    exact (hunit.smul_left_cancel).mp (key.trans (smul_zero _).symm)
  have hall : ∀ x, D x = 0 := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ {ζ} := by
      have htop : Algebra.adjoin ℤ {ζ} = ⊤ := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top
        (IsCyclotomicExtension.zeta_spec 21 ℚ _root_.GlobalTheory.HostModel.E21)
      rw [htop]
      trivial
    have := Derivation.eqOn_adjoin (D1 := D.restrictScalars ℤ) (D2 := 0)
      (s := {ζ}) (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hDζ) hx
    simpa using this
  have hsub : Subsingleton (Ω[𝓞 _root_.GlobalTheory.HostModel.E21⁄𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)]) := by
    have htop := KaehlerDifferential.span_range_derivation (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21))
      (𝓞 _root_.GlobalTheory.HostModel.E21)
    have hbot : Submodule.span (𝓞 _root_.GlobalTheory.HostModel.E21) (Set.range D) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact hall x
    rw [hbot] at htop
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _) := htop ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule (𝓞 _root_.GlobalTheory.HostModel.E21) _) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) := ⟨hsub⟩
  haveI : Algebra.FiniteType (𝓞 (maximalRealSubfield _root_.GlobalTheory.HostModel.E21)) (𝓞 _root_.GlobalTheory.HostModel.E21) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  exact ⟨inferInstance, inferInstance⟩

def host : Host E21 where
  d := 7
  d_mod := by norm_num
  d_prime := by norm_num
  rt := sqrtNegSeven
  rt_sq := sqrtNegSeven_sq
  w0 := halfSqrtNegSeven
  two_weight_eq_one_add_root := by unfold sqrtNegSeven; ring
  bar := (IsCMField.ringOfIntegersComplexConj E21).toRingEquiv
  bar_eq _ := rfl
  unram := unramified_E21_over_maximalRealSubfield
  rt0 := Complex.I * (Real.sqrt 7 : ℝ)
  sqrt_neg_disc_sq := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem host_d : host.d = 7 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem host_rt : host.rt = sqrtNegSeven := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem host_w0_eq_halfSqrtNegSeven : host.w0 = halfSqrtNegSeven := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem host_rt0_eq_I_mul_sqrt_seven : host.rt0 = Complex.I * (Real.sqrt 7 : ℝ) := rfl

instance nonempty_host : Nonempty (Host E21) := ⟨host⟩

/- English proof (translation)
Rewrite using `[IsCyclotomicExtension.finrank E21 (Polynomial.cyclotomic.irreducible_rat (n := 21) (by norm_num))]`. Evaluate the decidable proposition.
-/
theorem finrank_rat_E21_eq_twelve : Module.finrank ℚ E21 = 12 := by
  rw [IsCyclotomicExtension.finrank E21 (Polynomial.cyclotomic.irreducible_rat (n := 21) (by norm_num))]
  decide

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (complexConj_eq_neg_of_sq_eq_neg (n := 7) (coe_sq_eq_neg sqrtNegSeven_sq))`.
-/
example : host.bar host.rt = -host.rt :=
  RingOfIntegers.ext (complexConj_eq_neg_of_sq_eq_neg (n := 7)
    (coe_sq_eq_neg sqrtNegSeven_sq))

/- English proof (translation)
Establish `h` using `sub_complexConj_eq_of_two_mul host.rt_sq host.two_weight_eq_one_add_root`. Express the relevant statement in the definitionally equal form `halfSqrtNegSeven - host.bar host.w0 = 2 * halfSqrtNegSeven - 1 at h`. Express the relevant statement in the definitionally equal form `halfSqrtNegSeven * host.bar host.w0 = 2`. Take the linear combination `-halfSqrtNegSeven * h - halfSqrtNegSeven_quadratic`.
-/
example : host.w0 * host.bar host.w0 = 2 := by
  have h := sub_complexConj_eq_of_two_mul host.rt_sq host.two_weight_eq_one_add_root
  change halfSqrtNegSeven - host.bar host.w0 = 2 * halfSqrtNegSeven - 1 at h
  change halfSqrtNegSeven * host.bar host.w0 = 2
  linear_combination -halfSqrtNegSeven * h - halfSqrtNegSeven_quadratic

/- English proof (translation)
The claim follows from `exists_embedding_rt_eq host`.
-/
example : ∃ τ : E21 →+* ℂ, τ (sqrtNegSeven : E21) = Complex.I * (Real.sqrt 7 : ℝ) := exists_embedding_rt_eq host

end GlobalTheory.HostModel
