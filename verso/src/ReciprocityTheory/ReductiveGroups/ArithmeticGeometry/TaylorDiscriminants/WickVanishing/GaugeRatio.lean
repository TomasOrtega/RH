import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogPoinc

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf

section Chars

variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]

/- English proof (translation)
Establish `h2 : algebraMap ℚ k (1 / 2) * 2 = 1`. Rewrite using `[show (2 : k) = algebraMap ℚ k 2 from (map_ofNat (algebraMap ℚ k) 2).symm, ← map_mul]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem two_mul_eq_zero {x : k} (h : 2 * x = 0) : x = 0 := by
  have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
    rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat (algebraMap ℚ k) 2).symm, ← map_mul]
    norm_num
  calc x = (algebraMap ℚ k (1 / 2) * 2) * x := by rw [h2, one_mul]
    _ = algebraMap ℚ k (1 / 2) * (2 * x) := by ring
    _ = 0 := by rw [h, mul_zero]

/- English proof (translation)
Apply `two_mul_eq_zero` to reduce the goal to its premises. Establish `h0` using `h a`. Establish `h1` using `h (a + 1)`. Establish `h2` using `h (a * a)`. Establish `h3` using `h (a * a + 1)`.

Simplify using `only [map_add, map_one, map_mul, star_add, star_one, star_mul] at h1 h2 h3`. Take the linear combination `(-1 : k) * (h3 - h2) + (s' a + s (star a) + s' (star a) - s a) * (h1 - h0)`.
-/
theorem pair_prod (c : k) (s s' : O →+* k)
    (h : ∀ a, c * (s a * s (star a) + s' a * s' (star a) - 2 * s a * s' a) = 0) (a : O) :
    c * ((s a - s (star a)) * (s a - s' (star a))) = 0 := by
  apply two_mul_eq_zero
  have h0 := h a
  have h1 := h (a + 1)
  have h2 := h (a * a)
  have h3 := h (a * a + 1)
  simp only [map_add, map_one, map_mul, star_add, star_one, star_mul] at h1 h2 h3
  linear_combination (-1 : k) * (h3 - h2) + (s' a + s (star a) + s' (star a) - s a) * (h1 - h0)

variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨a₁, hu₁⟩` from `hunit σ τ₁ hne.1`. Take `⟨a₂, hu₂⟩` from `hunit σ τ₂ hne.2`. Establish `e1 : c * (χ σ a₁ - χ τ₂ a₁) = 0`.

Establish `h' : (χ σ a₁ - χ τ₁ a₁) * (c * (χ σ a₁ - χ τ₂ a₁)) = 0` using `by linear_combination P a₁`. Conclude with `hu₁.mul_right_eq_zero.1 h'`. Establish `e2 : c * (χ σ a₂ - χ τ₁ a₂) = 0`. Establish `h' : (χ σ a₂ - χ τ₂ a₂) * (c * (χ σ a₂ - χ τ₁ a₂)) = 0` using `by linear_combination P a₂`. Conclude with `hu₂.mul_right_eq_zero.1 h'`.

Establish `e3` using `P (a₁ + a₂)`. Simplify using `only [map_add] at e3`. Establish `e4 : ((χ σ a₁ - χ τ₁ a₁) * (χ σ a₂ - χ τ₂ a₂)) * c = 0`. Take the linear combination `e3 - ((χ σ a₁ - χ τ₁ a₁) + (χ σ a₂ - χ τ₁ a₂)) * e1 - (χ σ a₂ - χ τ₂ a₂) * e2`. Conclude with `hc ((hu₁.mul hu₂).mul_right_eq_zero.1 e4)`.
-/
theorem either {c : k} (hc : c ≠ 0) (σ τ₁ τ₂ : T)
    (P : ∀ a, c * ((χ σ a - χ τ₁ a) * (χ σ a - χ τ₂ a)) = 0) : σ = τ₁ ∨ σ = τ₂ := by
  by_contra hne
  push_neg at hne
  obtain ⟨a₁, hu₁⟩ := hunit σ τ₁ hne.1
  obtain ⟨a₂, hu₂⟩ := hunit σ τ₂ hne.2
  have e1 : c * (χ σ a₁ - χ τ₂ a₁) = 0 := by
    have h' : (χ σ a₁ - χ τ₁ a₁) * (c * (χ σ a₁ - χ τ₂ a₁)) = 0 := by linear_combination P a₁
    exact hu₁.mul_right_eq_zero.1 h'
  have e2 : c * (χ σ a₂ - χ τ₁ a₂) = 0 := by
    have h' : (χ σ a₂ - χ τ₂ a₂) * (c * (χ σ a₂ - χ τ₁ a₂)) = 0 := by linear_combination P a₂
    exact hu₂.mul_right_eq_zero.1 h'
  have e3 := P (a₁ + a₂)
  simp only [map_add] at e3
  have e4 : ((χ σ a₁ - χ τ₁ a₁) * (χ σ a₂ - χ τ₂ a₂)) * c = 0 := by
    linear_combination e3 - ((χ σ a₁ - χ τ₁ a₁) + (χ σ a₂ - χ τ₁ a₂)) * e1 - (χ σ a₂ - χ τ₂ a₂) * e2
  exact hc ((hu₁.mul hu₂).mul_right_eq_zero.1 e4)

include hcc in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨a, ha⟩` from `hunit _ _ hne`. Rewrite `ha` using `[hcc, hcc, star_star, sub_self]`. Establish `h01` using `isUnit_zero_iff.1 ha`. Apply `hc` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem cc_cc {c : k} (hc : c ≠ 0) (σ : T) : cc (cc σ) = σ := by
  by_contra hne
  obtain ⟨a, ha⟩ := hunit _ _ hne
  rw [hcc, hcc, star_star, sub_self] at ha
  have h01 := isUnit_zero_iff.1 ha
  apply hc
  calc c = c * 1 := (mul_one c).symm
    _ = c * 0 := by rw [h01]
    _ = 0 := mul_zero c

include hcc in

/- English proof (translation)
Establish `P1 : ∀ a, c * ((χ σ a - χ (cc σ) a) * (χ σ a - χ (cc σ') a)) = 0`. Introduce `a`. Rewrite using `[hcc, hcc]`. Conclude with `pair_prod c (χ σ) (χ σ') h a`. Establish `h' : ∀ a, c * (χ σ' a * χ σ' (star a) + χ σ a * χ σ (star a) - 2 * χ σ' a * χ σ a) = 0`.

Introduce `a`. Take the linear combination `h a`. Establish `P2 : ∀ a, c * ((χ σ' a - χ (cc σ') a) * (χ σ' a - χ (cc σ) a)) = 0`. Introduce `a`. Rewrite using `[hcc, hcc]`.

Conclude with `pair_prod c (χ σ') (χ σ) h' a`. Break down `either χ hunit hc σ _ _ P1 with h1 | h1` into its components or cases. Break down `either χ hunit hc σ' _ _ P2 with h2 | h2` into its components or cases. Assume the negation of the conclusion as `hne`. Establish `hne' : σ ≠ σ'` using `fun e => hne (by rw [← e]; exact h1)`.

Take `⟨a, ha⟩` from `hunit σ σ' hne'`. Establish `hs : χ σ (star a) = χ σ a` using `by rw [← hcc, ← h1]`. Establish `hs' : χ σ' (star a) = χ σ' a` using `by rw [← hcc, ← h2]`. Establish `e` using `h a`. Rewrite `e` using `[hs, hs']`.

Establish `e' : ((χ σ a - χ σ' a) * (χ σ a - χ σ' a)) * c = 0` using `by linear_combination e`. Conclude with `hc ((ha.mul ha).mul_right_eq_zero.1 e')`. Conclude with `h2`. Rewrite using `[h1, cc_cc χ cc hcc hunit hc]`.
-/
theorem pair_index {c : k} (hc : c ≠ 0) (σ σ' : T)
    (h : ∀ a, c * (χ σ a * χ σ (star a) + χ σ' a * χ σ' (star a) - 2 * χ σ a * χ σ' a) = 0) : σ' = cc σ := by
  have P1 : ∀ a, c * ((χ σ a - χ (cc σ) a) * (χ σ a - χ (cc σ') a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ) (χ σ') h a
  have h' : ∀ a, c * (χ σ' a * χ σ' (star a) + χ σ a * χ σ (star a) - 2 * χ σ' a * χ σ a) = 0 := by
    intro a
    linear_combination h a
  have P2 : ∀ a, c * ((χ σ' a - χ (cc σ') a) * (χ σ' a - χ (cc σ) a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ') (χ σ) h' a
  rcases either χ hunit hc σ _ _ P1 with h1 | h1
  · rcases either χ hunit hc σ' _ _ P2 with h2 | h2
    · by_contra hne
      have hne' : σ ≠ σ' := fun e => hne (by rw [← e]; exact h1)
      obtain ⟨a, ha⟩ := hunit σ σ' hne'
      have hs : χ σ (star a) = χ σ a := by rw [← hcc, ← h1]
      have hs' : χ σ' (star a) = χ σ' a := by rw [← hcc, ← h2]
      have e := h a
      rw [hs, hs'] at e
      have e' : ((χ σ a - χ σ' a) * (χ σ a - χ σ' a)) * c = 0 := by linear_combination e
      exact hc ((ha.mul ha).mul_right_eq_zero.1 e')
    · exact h2
  · rw [h1, cc_cc χ cc hcc hunit hc]

end Chars

section Series

variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)

/- English proof (translation)
Unfold `scaleBy`. Rewrite using `[MvPowerSeries.coeff_rescale]`.
-/
theorem coeff_scale (a : O) (f : MvPowerSeries (GLet T rk) k) (m : GLet T rk →₀ ℕ) :
    coeff m (scaleBy χ a f) = (m.prod fun l e => χ l.1 a ^ e) * coeff m f := by
  unfold scaleBy
  rw [MvPowerSeries.coeff_rescale]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_scale, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]`.
-/
theorem cc_scale (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    constantCoeff (scaleBy χ a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_scale,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]

/- English proof (translation)
Unfold `scaleBy`. Rewrite using `[MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst]`. Use `WickVanishing.subst_exp _ (fun s => ?_) hf` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem scale_exp (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    scaleBy χ a (PowerSeries.subst f (PowerSeries.exp k)) = PowerSeries.subst (scaleBy χ a f) (PowerSeries.exp k) := by
  unfold scaleBy
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst]
  refine WickVanishing.subst_exp _ (fun s => ?_) hf
  simp

/- English proof (translation)
Unfold `Finsupp.prod Finsupp.degree`. Conclude with `Finset.prod_pow_eq_pow_sum _ _ _`.
-/
theorem prod_two_pow (m : GLet T rk →₀ ℕ) : (m.prod fun _ e => (2 : k) ^ e) = 2 ^ m.degree := by
  unfold Finsupp.prod Finsupp.degree
  exact Finset.prod_pow_eq_pow_sum _ _ _

/- English proof (translation)
Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp), Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp), pow_one, pow_one]`.
-/
theorem prod_pair (g : GLet T rk → k) (l l' : GLet T rk) :
    ((Finsupp.single l 1 + Finsupp.single l' 1).prod fun l e => g l ^ e) = g l * g l' := by
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp),
    Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp), pow_one, pow_one]

/- English proof (translation)
Establish `hq : ((2 : ℚ) ^ n - 4) ≠ 0`. Introduce `h0`. Establish `h4 : (2 : ℚ) ^ n = 2 ^ 2` using `by linarith`. Conclude with `hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h4))`. Establish `e : algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x = 0`.

Rewrite using `[map_sub, map_pow, map_ofNat (algebraMap ℚ k) 2, map_ofNat (algebraMap ℚ k) 4]`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hq, map_one, one_mul]`. Use `_ = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹) * (algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x) := by`.

Rewrite using `[map_mul, mul_assoc]`. Use `_ = 0 := by rw [e, mul_zero]`.
-/
theorem eq_zero_of_pow_sub {n : ℕ} (hn : n ≠ 2) {x : k} (h : ((2 : k) ^ n - 4) * x = 0) : x = 0 := by
  have hq : ((2 : ℚ) ^ n - 4) ≠ 0 := by
    intro h0
    have h4 : (2 : ℚ) ^ n = 2 ^ 2 := by linarith
    exact hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h4))
  have e : algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x = 0 := by
    rw [map_sub, map_pow, map_ofNat (algebraMap ℚ k) 2, map_ofNat (algebraMap ℚ k) 4]
    exact h
  calc x = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹ * ((2 : ℚ) ^ n - 4)) * x := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹) * (algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [e, mul_zero]

end Series

/- English proof (translation)
Unfold `GaugeRatioSt`. Introduce `O _ _ k _ _ T _ rk χ cc hcc hunit r hr hfe`. Take `⟨q, hq0, hrq⟩ : ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧ r = PowerSeries.subst q (PowerSeries.exp k)` from `⟨_, WickVanishing.constantCoeff_logS hr, (WickVanishing.exp_log hr).symm⟩`. Establish `hA : ∀ b : O, constantCoeff (scaleBy χ b q) = 0` using `fun b => cc_scale χ b hq0`. Establish `hE : ∀ b : O, scaleBy χ b r = PowerSeries.subst (scaleBy χ b q) (PowerSeries.exp k)`.

Introduce `b`. Rewrite using `[hrq]`. Conclude with `scale_exp χ b hq0`. Establish `key : ∀ a : O, scaleBy χ (1 + a * star a) q = scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q`. Introduce `a`.

Establish `h1` using `hfe a`. Rewrite `h1` using `[hE, hE, hE]`. Rewrite `h1` using `[hrq]`. Establish `s1 : constantCoeff (scaleBy χ a q + scaleBy χ a q) = 0` using `by rw [map_add, hA, add_zero]`. Establish `s2 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q) = 0` using `by rw [map_add, s1, hq0, add_zero]`.

Establish `s3 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q) = 0`. Rewrite using `[map_add, s2, hA, add_zero]`. Apply `WickVanishing.exp_inj (hA _) s3` to reduce the goal to its premises. Rewrite using `[h1, WickVanishing.exp_add s2 (hA _), WickVanishing.exp_add s1 hq0, WickVanishing.exp_add (hA _) (hA _)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcoef : ∀ (a : O) (m : GLet T rk →₀ ℕ), (m.prod fun l e => χ l.1 (1 + a * star a) ^ e) * coeff m q = ((m.prod fun l e => χ l.1 a ^ e) + (m.prod fun l e => χ l.1 a ^ e) + 1 + (m.prod fun l e => χ l.1 (a * star a) ^ e)) * coeff m q`. Introduce `a m`. Establish `h` using `congrArg (fun f => coeff m f) (key a)`. Rewrite `h` using `[map_add, map_add, map_add]`. Simplify using `only [coeff_scale] at h`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨q, hq0, ?_, ?_, hrq⟩` and prove the remaining obligations. Introduce `m hm`. Assume the negation of the conclusion as `hdeg`.

Establish `h` using `hcoef 1 m`. Establish `t2 : ∀ l : GLet T rk, χ l.1 (1 + 1) = 2` using `fun l => by`. Rewrite using `[map_add, map_one, one_add_one_eq_two]`. Establish `t1 : ∀ l : GLet T rk, χ l.1 1 = 1` using `fun l => map_one _`. Simplify using `only [star_one, mul_one, t1, one_pow] at h`.

Simplify using `only [t2] at h`. Rewrite `h` using `[prod_two_pow (k := k) m]`. Establish `p1 : (m.prod fun (_ : GLet T rk) (_ : ℕ) => (1 : k)) = 1` using `by simp [Finsupp.prod]`. Rewrite `h` using `[p1]`. Conclude with `hm (eq_zero_of_pow_sub hdeg (by linear_combination h))`.

Introduce `l l' hne`. Use `pair_index χ cc hcc hunit hne l.1 l'.1 (fun a => ?_)` and prove the remaining obligations. Establish `h` using `hcoef a (Finsupp.single l 1 + Finsupp.single l' 1)`. Rewrite `h` using `[prod_pair, prod_pair, prod_pair]`. Simplify using `only [map_add, map_one, map_mul] at h`.

Take the linear combination `h`.
-/
theorem gaugeRatio : GaugeRatioSt := by
  unfold GaugeRatioSt
  intro O _ _ k _ _ T _ rk χ cc hcc hunit r hr hfe
  obtain ⟨q, hq0, hrq⟩ : ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      r = PowerSeries.subst q (PowerSeries.exp k) :=
    ⟨_, WickVanishing.constantCoeff_logS hr, (WickVanishing.exp_log hr).symm⟩
  have hA : ∀ b : O, constantCoeff (scaleBy χ b q) = 0 := fun b => cc_scale χ b hq0
  have hE : ∀ b : O, scaleBy χ b r = PowerSeries.subst (scaleBy χ b q) (PowerSeries.exp k) := by
    intro b
    rw [hrq]
    exact scale_exp χ b hq0
  have key : ∀ a : O, scaleBy χ (1 + a * star a) q =
      scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q := by
    intro a
    have h1 := hfe a
    rw [hE, hE, hE] at h1
    rw [hrq] at h1
    have s1 : constantCoeff (scaleBy χ a q + scaleBy χ a q) = 0 := by rw [map_add, hA, add_zero]
    have s2 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q) = 0 := by rw [map_add, s1, hq0, add_zero]
    have s3 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q) = 0 := by
      rw [map_add, s2, hA, add_zero]
    apply WickVanishing.exp_inj (hA _) s3
    rw [h1, WickVanishing.exp_add s2 (hA _), WickVanishing.exp_add s1 hq0, WickVanishing.exp_add (hA _) (hA _)]
    ring
  have hcoef : ∀ (a : O) (m : GLet T rk →₀ ℕ),
      (m.prod fun l e => χ l.1 (1 + a * star a) ^ e) * coeff m q =
        ((m.prod fun l e => χ l.1 a ^ e) + (m.prod fun l e => χ l.1 a ^ e) + 1 +
          (m.prod fun l e => χ l.1 (a * star a) ^ e)) * coeff m q := by
    intro a m
    have h := congrArg (fun f => coeff m f) (key a)
    rw [map_add, map_add, map_add] at h
    simp only [coeff_scale] at h
    rw [h]
    ring
  refine ⟨q, hq0, ?_, ?_, hrq⟩
  · intro m hm
    by_contra hdeg
    have h := hcoef 1 m
    have t2 : ∀ l : GLet T rk, χ l.1 (1 + 1) = 2 := fun l => by
      rw [map_add, map_one, one_add_one_eq_two]
    have t1 : ∀ l : GLet T rk, χ l.1 1 = 1 := fun l => map_one _
    simp only [star_one, mul_one, t1, one_pow] at h
    simp only [t2] at h
    rw [prod_two_pow (k := k) m] at h
    have p1 : (m.prod fun (_ : GLet T rk) (_ : ℕ) => (1 : k)) = 1 := by simp [Finsupp.prod]
    rw [p1] at h
    exact hm (eq_zero_of_pow_sub hdeg (by linear_combination h))
  · intro l l' hne
    refine pair_index χ cc hcc hunit hne l.1 l'.1 (fun a => ?_)
    have h := hcoef a (Finsupp.single l 1 + Finsupp.single l' 1)
    rw [prod_pair, prod_pair, prod_pair] at h
    simp only [map_add, map_one, map_mul] at h
    linear_combination h

end ReciprocityTheory.ChartRestriction.G.TB.GRPf
