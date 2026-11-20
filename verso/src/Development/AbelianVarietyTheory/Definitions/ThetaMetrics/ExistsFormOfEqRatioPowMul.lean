import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace.Model

variable {R : Type} [CommRing R] {N : ℕ}

/- English proof (translation)
Take `⟨p, rfl⟩` from `(chartAlgEquiv R N i).surjective u`. Take `⟨n, f, hf, h⟩` from `HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) (polyToAway R N i p)`. Use `⟨n, f, by simpa using hf, ?_⟩` and prove the remaining obligations. Rewrite using `[chartAlgEquiv_apply, ← h, awayToSection_mk]`. Conclude with `frac_eq rfl`.
-/
theorem exists_formOn (i : Fin (N + 1)) (u : Γ(PSpace R N, chart R N i)) :
    ∃ n f, ∃ hf : (f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous n,
      u = formOn (chart R N i) i le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N i).surjective u
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) (polyToAway R N i p)
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [chartAlgEquiv_apply, ← h, awayToSection_mk]
  exact frac_eq rfl

/- English proof (translation)
Establish `hb : (PSpace R N).basicOpen (ratio R N i j) = U` using `basicOpen_ratioOn.trans hU.symm`. Substitute `hb` using the available equality. Establish `hl` using `(isAffineOpen_chart R N i).isLocalization_basicOpen (ratio R N i j)`. Establish `hreg : ratio R N i j ∈ nonZeroDivisors _`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Rewrite using `[ratio, ratioOn_self]`. Conclude with `one_mem _`. Rewrite using `[← chartAlgEquiv_X R N i ⟨j, h⟩]`. Use `mem_nonZeroDivisors_iff_right.2 fun x hx => ?_` and prove the remaining obligations.

Take `⟨p, rfl⟩` from `(chartAlgEquiv R N i).surjective x`. Rewrite `hx` using `[← map_mul, map_eq_zero_iff _ (chartAlgEquiv R N i).injective]`. Establish `: p = 0` using `(isRegular_X (n := (⟨j, h⟩ : {k // k ≠ i}))).right (by simpa using hx)`. Simplify using `[this]`. Conclude with `IsLocalization.injective (M := Submonoid.powers (ratio R N i j)) Γ(PSpace R N, (PSpace R N).basicOpen (ratio R N i j)) (Submonoid.powers_le.2 hreg)`.
-/
theorem resG_overlap_injective (i j : Fin (N + 1)) {U : (PSpace R N).Opens} (hi : U ≤ chart R N i)
    (hU : U = chart R N i ⊓ chart R N j) : Function.Injective (resG (PSpace R N) hi) := by
  have hb : (PSpace R N).basicOpen (ratio R N i j) = U := basicOpen_ratioOn.trans hU.symm
  subst hb
  have hl := (isAffineOpen_chart R N i).isLocalization_basicOpen (ratio R N i j)
  have hreg : ratio R N i j ∈ nonZeroDivisors _ := by
    by_cases h : j = i
    · subst h; rw [ratio, ratioOn_self]; exact one_mem _
    · rw [← chartAlgEquiv_X R N i ⟨j, h⟩]
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
      obtain ⟨p, rfl⟩ := (chartAlgEquiv R N i).surjective x
      rw [← map_mul, map_eq_zero_iff _ (chartAlgEquiv R N i).injective] at hx
      have : p = 0 := (isRegular_X (n := (⟨j, h⟩ : {k // k ≠ i}))).right (by simpa using hx)
      simp [this]
  exact IsLocalization.injective (M := Submonoid.powers (ratio R N i j))
    Γ(PSpace R N, (PSpace R N).basicOpen (ratio R N i j)) (Submonoid.powers_le.2 hreg)

/- English proof (translation)
Take `⟨a, F, hF, rfl⟩` from `exists_formOn i u`. Take `⟨b, G, hG, rfl⟩` from `exists_formOn j v`. Establish `hL : (F * X j ^ (k + 1 + b)).IsHomogeneous (a + (k + 1 + b))` using `hF.mul (isHomogeneous_X_pow _ _)`. Establish `hR : (G * X i ^ (a + k + 1)).IsHomogeneous (a + (k + 1 + b))`. Use `hG.mul (isHomogeneous_X_pow (R := R) i (a + k + 1))` as an intermediate fact.

Rewrite `this` using `[show b + (a + k + 1) = a + (k + 1 + b) by ring]`. Then use the resulting hypothesis. Establish `key : F * X j ^ (k + 1 + b) = G * X i ^ (a + k + 1)`. Use `(formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)` and prove the remaining obligations. Rewrite using `[resG_formOn, resG_formOn]`. Rewrite `h` using `[resG_formOn, resG_formOn]`.

Establish `e1 : formOn U i hi (a + (k + 1 + b)) _ hL = formOn U i hi a F hF * ratioOn U i hi j ^ (k + 1) * ratioOn U i hi j ^ b`. Simplify using `only [formOn_eq_aeval, map_mul, map_pow, aeval_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : formOn U i hi (a + (k + 1 + b)) _ hR = formOn U i hi b G hG`. Simplify using `only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG, mul_comm]`. Establish `hF0 : F = 0`. Use extensionality with `m`. Assume the negation of the conclusion as `hm`.

Establish `hdeg` using `hF hm`. Establish `hle : m i ≤ a`. Rewrite using `[← hdeg]`. Conclude with `Finsupp.le_weight _ (s := i) one_ne_zero m`. Use `congrArg (coeff (m + Finsupp.single j (k + 1 + b))) key` as an intermediate fact.

Rewrite `this` using `[X_pow_eq_monomial, X_pow_eq_monomial, coeff_mul_monomial, coeff_mul_monomial', if_neg]`. Conclude with `hm (by simpa using this)`. Introduce `hle'`. Use `hle' i` as an intermediate fact. Simplify using `[Finsupp.single_apply, hij] at this`.

Use linear arithmetic over natural numbers and integers. Substitute `hF0` using the available equality. Conclude with `formOn_zero`.
-/
theorem eq_zero_of_mul_ratio_pow {i j : Fin (N + 1)} (hij : j ≠ i) (k : ℕ) {U : (PSpace R N).Opens}
    (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) (hU : U = chart R N i ⊓ chart R N j)
    (u : Γ(PSpace R N, chart R N i)) (v : Γ(PSpace R N, chart R N j))
    (h : resG _ hi u * ratioOn U i hi j ^ (k + 1) = resG _ hj v) : u = 0 := by
  obtain ⟨a, F, hF, rfl⟩ := exists_formOn i u
  obtain ⟨b, G, hG, rfl⟩ := exists_formOn j v
  have hL : (F * X j ^ (k + 1 + b)).IsHomogeneous (a + (k + 1 + b)) := hF.mul (isHomogeneous_X_pow _ _)
  have hR : (G * X i ^ (a + k + 1)).IsHomogeneous (a + (k + 1 + b)) := by
    have := hG.mul (isHomogeneous_X_pow (R := R) i (a + k + 1))
    rwa [show b + (a + k + 1) = a + (k + 1 + b) by ring] at this
  have key : F * X j ^ (k + 1 + b) = G * X i ^ (a + k + 1) := by
    refine (formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)
    rw [resG_formOn, resG_formOn]
    rw [resG_formOn, resG_formOn] at h
    have e1 : formOn U i hi (a + (k + 1 + b)) _ hL =
        formOn U i hi a F hF * ratioOn U i hi j ^ (k + 1) * ratioOn U i hi j ^ b := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X]; ring
    have e2 : formOn U i hi (a + (k + 1 + b)) _ hR = formOn U i hi b G hG := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    rw [e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG, mul_comm]
  have hF0 : F = 0 := by
    ext m
    by_contra hm
    have hdeg := hF hm
    have hle : m i ≤ a := by
      rw [← hdeg]
      exact Finsupp.le_weight _ (s := i) one_ne_zero m
    have := congrArg (coeff (m + Finsupp.single j (k + 1 + b))) key
    rw [X_pow_eq_monomial, X_pow_eq_monomial, coeff_mul_monomial, coeff_mul_monomial', if_neg] at this
    · exact hm (by simpa using this)
    · intro hle'
      have := hle' i
      simp [Finsupp.single_apply, hij] at this
      omega
  subst hF0
  exact formOn_zero

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_ne (i PUnit.unit)`. Establish `hUi` using `On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) i`. Establish `hUj` using `On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) (fun _ => j)`. Establish `hc` using `s.compat i (fun _ => j)`. Rewrite `hc` using `[On_g, zpow_neg, zpow_natCast]`.

Establish `h0` using `eq_zero_of_mul_ratio_pow hj k (inf_le_left.trans hUi.le) (inf_le_right.trans hUj.le) (by rw [hUi, hUj]) (resG _ hUi.ge (s.f i)) (resG _ hUj.ge (s.f fun _ => j)) (by`. Establish `e1 : resG _ (inf_le_left.trans hUi.le : _ ⊓ (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U (fun _ => j) ≤ _) (resG _ hUi.ge (s.f i)) = resG _ inf_le_left (s.f i)` using `rfl`. Establish `e2 : resG _ (inf_le_right.trans hUj.le : (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U i ⊓ _ ≤ _) (resG _ hUj.ge (s.f fun _ => j)) = resG _ inf_le_right (s.f fun _ => j)` using `rfl`. Rewrite using `[e1, e2]`. Use `erw [hc]`.

Rewrite using `[← val_ratioUnit (hj := inf_le_right.trans hUj.le), ← Units.val_pow_eq_pow_val, mul_right_comm, Units.inv_mul, one_mul])`. Establish `e : s.f i = resG _ hUi.le (resG _ hUi.ge (s.f i))` using `rfl`. Rewrite using `[e, h0, map_zero]`.
-/
theorem sec_neg_eq_zero (k : ℕ) (s : (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).Sec)
    (i : PUnit → Fin (N + 2)) : s.f i = 0 := by
  obtain ⟨j, hj⟩ := exists_ne (i PUnit.unit)
  have hUi := On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) i
  have hUj := On_U R (N + 1) (-((k + 1 : ℕ) : ℤ)) (fun _ => j)
  have hc := s.compat i (fun _ => j)
  rw [On_g, zpow_neg, zpow_natCast] at hc
  have h0 := eq_zero_of_mul_ratio_pow hj k (inf_le_left.trans hUi.le) (inf_le_right.trans hUj.le)
    (by rw [hUi, hUj]) (resG _ hUi.ge (s.f i)) (resG _ hUj.ge (s.f fun _ => j)) (by
      have e1 : resG _ (inf_le_left.trans hUi.le : _ ⊓ (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U (fun _ => j) ≤ _)
          (resG _ hUi.ge (s.f i)) = resG _ inf_le_left (s.f i) := rfl
      have e2 : resG _ (inf_le_right.trans hUj.le : (On R (N + 1) (-((k + 1 : ℕ) : ℤ))).U i ⊓ _ ≤ _)
          (resG _ hUj.ge (s.f fun _ => j)) = resG _ inf_le_right (s.f fun _ => j) := rfl
      rw [e1, e2]
      erw [hc]
      rw [← val_ratioUnit (hj := inf_le_right.trans hUj.le), ← Units.val_pow_eq_pow_val, mul_right_comm,
        Units.inv_mul, one_mul])
  have e : s.f i = resG _ hUi.le (resG _ hUi.ge (s.f i)) := rfl
  rw [e, h0, map_zero]

/- English proof (translation)
Take `⟨a, F, hF, rfl⟩` from `exists_formOn i u`. Take `⟨b, G, hG, rfl⟩` from `exists_formOn j v`. Establish `hH : (F * X i ^ n).IsHomogeneous (a + n)` using `hF.mul (isHomogeneous_X_pow _ _)`. Establish `hL : (F * X i ^ n * X j ^ b).IsHomogeneous (a + n + b)` using `hH.mul (isHomogeneous_X_pow _ _)`. Establish `hR : (G * X j ^ n * X i ^ a).IsHomogeneous (a + n + b)`.

Use `(hG.mul (isHomogeneous_X_pow (R := R) j n)).mul (isHomogeneous_X_pow (R := R) i a)` as an intermediate fact. Rewrite `this` using `[show b + n + a = a + n + b by ring]`. Then use the resulting hypothesis. Establish `key : F * X i ^ n * X j ^ b = G * X j ^ n * X i ^ a`. Use `(formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)` and prove the remaining obligations. Rewrite using `[resG_formOn, resG_formOn]`.

Rewrite `h` using `[resG_formOn, resG_formOn]`. Establish `e1 : formOn U i hi (a + n + b) _ hL = formOn U i hi a F hF * ratioOn U i hi j ^ b`. Simplify using `only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : formOn U i hi (a + n + b) _ hR = formOn U i hi b G hG * ratioOn U i hi j ^ n`.

Simplify using `only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmod : (F * X i ^ n).modMonomial (Finsupp.single i a) = 0`.

Use extensionality with `m`. Distinguish the cases in `hm : Finsupp.single i a ≤ m`. Rewrite using `[coeff_modMonomial_of_le _ hm, coeff_zero]`. Rewrite using `[coeff_modMonomial_of_not_le _ hm, coeff_zero]`. Use `congrArg (coeff (m + Finsupp.single j b)) key` as an intermediate fact.

Rewrite `this` using `[X_pow_eq_monomial (n := j) (e := b), X_pow_eq_monomial (n := i) (e := a), coeff_mul_monomial, coeff_mul_monomial', if_neg]`. Simplify using `using this`. Introduce `hle'`. Use `hle' i` as an intermediate fact. Simplify using `[hij] at this`.

Conclude with `hm (Finsupp.single_le_iff.2 this)`. Establish `hdiv` using `divMonomial_add_modMonomial (F * X i ^ n) (Finsupp.single i a)`. Rewrite `hdiv` using `[hmod, add_zero, ← X_pow_eq_monomial]`. Establish `hf : ((F * X i ^ n).divMonomial (Finsupp.single i a)).IsHomogeneous n`. Introduce `m hm`.

Rewrite `hm` using `[coeff_divMonomial]`. Use `hH hm` as an intermediate fact. Rewrite `this` using `[map_add, Finsupp.weight_single]`. Simplify using `using this`. Use `⟨_, hf, ?_⟩` and prove the remaining obligations.

Use `congrArg (aeval (R := R) (ratioOn (chart R N i) i le_rfl)) hdiv` as an intermediate fact. Simplify using `only [map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul, mul_one] at this`. Rewrite using `[formOn_eq_aeval, formOn_eq_aeval, this]`.
-/
theorem exists_form_of_eq_ratio_pow_mul {i j : Fin (N + 1)} (hij : j ≠ i) (n : ℕ) {U : (PSpace R N).Opens}
    (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) (hU : U = chart R N i ⊓ chart R N j)
    (u : Γ(PSpace R N, chart R N i)) (v : Γ(PSpace R N, chart R N j))
    (h : resG _ hi u = ratioOn U i hi j ^ n * resG _ hj v) :
    ∃ f, ∃ hf : (f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous n,
      u = formOn (chart R N i) i le_rfl n f hf := by
  obtain ⟨a, F, hF, rfl⟩ := exists_formOn i u
  obtain ⟨b, G, hG, rfl⟩ := exists_formOn j v
  have hH : (F * X i ^ n).IsHomogeneous (a + n) := hF.mul (isHomogeneous_X_pow _ _)
  have hL : (F * X i ^ n * X j ^ b).IsHomogeneous (a + n + b) := hH.mul (isHomogeneous_X_pow _ _)
  have hR : (G * X j ^ n * X i ^ a).IsHomogeneous (a + n + b) := by
    have := (hG.mul (isHomogeneous_X_pow (R := R) j n)).mul (isHomogeneous_X_pow (R := R) i a)
    rwa [show b + n + a = a + n + b by ring] at this
  have key : F * X i ^ n * X j ^ b = G * X j ^ n * X i ^ a := by
    refine (formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)
    rw [resG_formOn, resG_formOn]
    rw [resG_formOn, resG_formOn] at h
    have e1 : formOn U i hi (a + n + b) _ hL = formOn U i hi a F hF * ratioOn U i hi j ^ b := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    have e2 : formOn U i hi (a + n + b) _ hR = formOn U i hi b G hG * ratioOn U i hi j ^ n := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    rw [e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG]; ring
  have hmod : (F * X i ^ n).modMonomial (Finsupp.single i a) = 0 := by
    ext m
    by_cases hm : Finsupp.single i a ≤ m
    · rw [coeff_modMonomial_of_le _ hm, coeff_zero]
    · rw [coeff_modMonomial_of_not_le _ hm, coeff_zero]
      have := congrArg (coeff (m + Finsupp.single j b)) key
      rw [X_pow_eq_monomial (n := j) (e := b), X_pow_eq_monomial (n := i) (e := a), coeff_mul_monomial,
        coeff_mul_monomial', if_neg] at this
      · simpa using this
      · intro hle'
        have := hle' i
        simp [hij] at this
        exact hm (Finsupp.single_le_iff.2 this)
  have hdiv := divMonomial_add_modMonomial (F * X i ^ n) (Finsupp.single i a)
  rw [hmod, add_zero, ← X_pow_eq_monomial] at hdiv
  have hf : ((F * X i ^ n).divMonomial (Finsupp.single i a)).IsHomogeneous n := by
    intro m hm
    rw [coeff_divMonomial] at hm
    have := hH hm
    rw [map_add, Finsupp.weight_single] at this
    simpa using this
  refine ⟨_, hf, ?_⟩
  have := congrArg (aeval (R := R) (ratioOn (chart R N i) i le_rfl)) hdiv
  simp only [map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul, mul_one] at this
  rw [formOn_eq_aeval, formOn_eq_aeval, this]

/- English proof (translation)
Establish `hU` using `On_U R (N + 1) n`. Establish `hc : ∀ i j : PUnit → Fin (N + 2), resG _ (inf_le_left.trans (hU i).le : _ ⊓ (On R (N + 1) n).U j ≤ _) (resG _ (hU i).ge (s.f i)) = ratioOn _ _ (inf_le_left.trans (hU i).le) (j PUnit.unit) ^ n * resG _ (inf_le_right.trans (hU j).le) (resG _ (hU j).ge (s.f j))`. Introduce `i j`. Establish `e` using `On_g R (N + 1) n i j`. Rewrite `e` using `[zpow_natCast]`.

Establish `e'` using `(congrArg Units.val e).trans (Units.val_pow_eq_pow_val _ _)`. Conclude with `(s.compat i j).trans (congrArg (· * _) e')`. Take `⟨f, hf, h0⟩` from `exists_form_of_eq_ratio_pow_mul (i := 0) (j := 1) (by simp) n _ _ (by rw [hU, hU]) _ _ (hc (fun _ => 0) (fun _ => 1))`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Establish `hk : ∀ k : PUnit → Fin (N + 2), resG _ (hU k).ge (s.f k) = formOn (chart R (N + 1) (k PUnit.unit)) _ le_rfl n f hf`.

Introduce `k`. Use `resG_overlap_injective (k PUnit.unit) 0 (inf_le_left.trans (hU k).le : _ ⊓ (On R (N + 1) n).U (fun _ => (0 : Fin (N + 2))) ≤ _) (by rw [hU, hU]) ?_` and prove the remaining obligations. Rewrite using `[hc k (fun _ => 0), h0, resG_formOn, resG_formOn]`. Conclude with `(formOn_eq_ratioOn_pow_mul _ hf).symm`. Take `⟨sf, sc⟩` from `s`.

Establish `: sf = (formSec n f hf).f` using `funext fun k => by`. Establish `e : sf k = resG _ (hU k).le (resG _ (hU k).ge (sf k))` using `rfl`. Conclude with `e.trans (congrArg (resG _ (hU k).le) (hk k))`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem exists_formSec (n : ℕ) (s : (lbPow (O1 R (N + 1)) n).Sec) :
    ∃ f, ∃ hf : (f : MvPolynomial (Fin (N + 2)) R).IsHomogeneous n, s = formSec n f hf := by
  have hU := On_U R (N + 1) n
  have hc : ∀ i j : PUnit → Fin (N + 2),
      resG _ (inf_le_left.trans (hU i).le : _ ⊓ (On R (N + 1) n).U j ≤ _) (resG _ (hU i).ge (s.f i)) =
      ratioOn _ _ (inf_le_left.trans (hU i).le) (j PUnit.unit) ^ n *
        resG _ (inf_le_right.trans (hU j).le) (resG _ (hU j).ge (s.f j)) := by
    intro i j
    have e := On_g R (N + 1) n i j
    rw [zpow_natCast] at e
    have e' := (congrArg Units.val e).trans (Units.val_pow_eq_pow_val _ _)
    exact (s.compat i j).trans (congrArg (· * _) e')
  obtain ⟨f, hf, h0⟩ := exists_form_of_eq_ratio_pow_mul (i := 0) (j := 1) (by simp) n _ _
    (by rw [hU, hU]) _ _ (hc (fun _ => 0) (fun _ => 1))
  refine ⟨f, hf, ?_⟩
  have hk : ∀ k : PUnit → Fin (N + 2), resG _ (hU k).ge (s.f k) =
      formOn (chart R (N + 1) (k PUnit.unit)) _ le_rfl n f hf := by
    intro k
    refine resG_overlap_injective (k PUnit.unit) 0
      (inf_le_left.trans (hU k).le : _ ⊓ (On R (N + 1) n).U (fun _ => (0 : Fin (N + 2))) ≤ _) (by rw [hU, hU]) ?_
    rw [hc k (fun _ => 0), h0, resG_formOn, resG_formOn]
    exact (formOn_eq_ratioOn_pow_mul _ hf).symm
  obtain ⟨sf, sc⟩ := s
  have : sf = (formSec n f hf).f := funext fun k => by
    have e : sf k = resG _ (hU k).le (resG _ (hU k).ge (sf k)) := rfl
    exact e.trans (congrArg (resG _ (hU k).le) (hk k))
  subst this
  rfl

/- English proof (translation)
Introduce `ht`. Establish `h` using `ht (0 : Fin (N + 2)) (1 : Fin (N + 2))`. Establish `h0` using `eq_zero_of_mul_ratio_pow (R := R) (i := (0 : Fin (N + 2))) (j := 1) (by simp) 0 inf_le_left inf_le_right rfl ((t.s (0 : Fin (N + 2)))⁻¹).val ((t.s (1 : Fin (N + 2)))⁻¹).val (by`. Establish `aux : ∀ {G : Type} [CommGroup G] (a g b : G), a = g * b → a⁻¹ * g = b⁻¹`. Introduce and unpack `G _ a g b rfl`.

Simplify using the standard rewrite rules. Establish `h'` using `aux _ _ _ h`. Rewrite `h'` using `[← map_inv, ← map_inv]`. Rewrite using `[zero_add, pow_one]`. Conclude with `congrArg Units.val h')`.

Use `haveI : Nontrivial Γ(PSpace R (N + 1), chart R (N + 1) 0) := (chartAlgEquiv R (N + 1) 0).symm.toEquiv.nontrivial`. Conclude with `Units.ne_zero _ h0`.
-/
theorem not_isGen_O1 [Nontrivial R] (t : (O1 R (N + 1)).Gen) : ¬ t.IsGen := by
  intro ht
  have h := ht (0 : Fin (N + 2)) (1 : Fin (N + 2))
  have h0 := eq_zero_of_mul_ratio_pow (R := R) (i := (0 : Fin (N + 2))) (j := 1) (by simp) 0
    inf_le_left inf_le_right rfl ((t.s (0 : Fin (N + 2)))⁻¹).val ((t.s (1 : Fin (N + 2)))⁻¹).val (by
      have aux : ∀ {G : Type} [CommGroup G] (a g b : G), a = g * b → a⁻¹ * g = b⁻¹ := by
        rintro G _ a g b rfl; simp
      have h' := aux _ _ _ h
      rw [← map_inv, ← map_inv] at h'
      rw [zero_add, pow_one]
      exact congrArg Units.val h')
  haveI : Nontrivial Γ(PSpace R (N + 1), chart R (N + 1) 0) :=
    (chartAlgEquiv R (N + 1) 0).symm.toEquiv.nontrivial
  exact Units.ne_zero _ h0

/- English proof (translation)
Use `⟨⟨fun _ => 1⟩, fun (i j : Fin 1) => ?_⟩` and prove the remaining obligations. Take `rfl : i = j` from `Subsingleton.elim _ _`. Rewrite using `[O1_g_eq_ratioUnit_chart_inf, ratioUnit_self, map_one]`. Conclude with `(one_mul _).symm`.
-/
theorem exists_isGen_O1_zero : ∃ t : (O1 R 0).Gen, t.IsGen := by
  refine ⟨⟨fun _ => 1⟩, fun (i j : Fin 1) => ?_⟩
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [O1_g_eq_ratioUnit_chart_inf, ratioUnit_self, map_one]
  exact (one_mul _).symm

/- English proof (translation)
Use `haveI : IsIso (chartι R 0 0) := by`. Use `isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_` and prove the remaining obligations. Rewrite using `[opensRange_chartι, ← iSup_chart R 0]`. Conclude with `(iSup_unique (ι := Fin 1) (f := chart R 0)).symm`. Use `haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim (α := Fin 1) _ _)⟩`.

Use `haveI : IsIso (chartι R 0 0 ≫ PSpace.str R 0) := by`. Rewrite using `[chartι_str]`. Conclude with `inferInstanceAs (IsIso (Spec.map (isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))`. Conclude with `IsIso.of_isIso_comp_left (chartι R 0 0) _`.
-/
theorem isIso_str_zero : IsIso (PSpace.str R 0) := by
  haveI : IsIso (chartι R 0 0) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [opensRange_chartι, ← iSup_chart R 0]
    exact (iSup_unique (ι := Fin 1) (f := chart R 0)).symm
  haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim (α := Fin 1) _ _)⟩
  haveI : IsIso (chartι R 0 0 ≫ PSpace.str R 0) := by
    rw [chartι_str]
    exact inferInstanceAs (IsIso (Spec.map
      (isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
  exact IsIso.of_isIso_comp_left (chartι R 0 0) _

/- English proof (translation)
Use `⟨fun e => ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (coeff (Finsupp.single 0 1)) ((formSec_inj _ _).1 e)` as an intermediate fact. Rewrite `this` using `[coeff_C_mul, coeff_X, if_pos rfl, coeff_zero]`. Conclude with `absurd this (by decide)`. Rewrite using `[nonzeroLocus_formSec]`.

Use `le_bot_iff.1 fun x hx => hx (x.isPrime.mem_of_pow_mem 2 ?_)` and prove the remaining obligations. Establish `: (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)) ^ 2 = 0`. Rewrite using `[mul_pow, ← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero, zero_mul]`. Rewrite using `[this]`. Conclude with `zero_mem _`.
-/
theorem nilpotent_form (h : (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)).IsHomogeneous 1) :
    formSec 1 _ h ≠ formSec 1 0 (isHomogeneous_zero _ _ 1) ∧ nonzeroLocus (formSec 1 _ h) = ⊥ := by
  refine ⟨fun e => ?_, ?_⟩
  · have := congrArg (coeff (Finsupp.single 0 1)) ((formSec_inj _ _).1 e)
    rw [coeff_C_mul, coeff_X, if_pos rfl, coeff_zero] at this
    exact absurd this (by decide)
  · rw [nonzeroLocus_formSec]
    refine le_bot_iff.1 fun x hx => hx (x.isPrime.mem_of_pow_mem 2 ?_)
    have : (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)) ^ 2 = 0 := by
      rw [mul_pow, ← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero, zero_mul]
    rw [this]; exact zero_mem _

/- English proof (translation)
The claim follows from `formOn_X (hi := (On_U R N 1 j).le)`.
-/
theorem formSec_X_f (k : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    (formSec 1 (X k) (isHomogeneous_X R k)).f j =
      resG _ (On_U R N 1 j).le ((coord R N k).f (j PUnit.unit)) :=
  formOn_X (hi := (On_U R N 1 j).le)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => x.isPrime.ne_top (Subsingleton.elim _ _)⟩`.
-/
theorem isEmpty_of_subsingleton [Subsingleton R] : IsEmpty (PSpace R N) :=
  ⟨fun x => x.isPrime.ne_top (Subsingleton.elim _ _)⟩

end GlobalTheory.ProjSpace.Model
