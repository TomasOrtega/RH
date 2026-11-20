import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F
namespace IsogenySigmaQuotient

variable (L : PeriodPair)

open Classical in

def ind (x : ℂ) : WithTop ℤ := if x ∈ L.lattice then 1 else 0

/- English proof (translation)
Simplify using `[ind, h]`.
-/
lemma ind_of_mem {x : ℂ} (h : x ∈ L.lattice) : ind L x = 1 := by
  simp [ind, h]

/- English proof (translation)
Simplify using `[ind, h]`.
-/
lemma ind_of_notMem {x : ℂ} (h : x ∉ L.lattice) : ind L x = 0 := by
  simp [ind, h]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ L.lattice`. Rewrite using `[ind_of_mem L hx, ind_of_mem L (L.lattice.neg_mem hx)]`. Rewrite using `[ind_of_notMem L hx, ind_of_notMem L (fun h => hx (by simpa using L.lattice.neg_mem h))]`.
-/
lemma ind_neg (x : ℂ) : ind L (-x) = ind L x := by
  by_cases hx : x ∈ L.lattice
  · rw [ind_of_mem L hx, ind_of_mem L (L.lattice.neg_mem hx)]
  · rw [ind_of_notMem L hx, ind_of_notMem L (fun h => hx (by simpa using L.lattice.neg_mem h))]

/- English proof (translation)
Establish `hd` using `(hb L).1`. Conclude with `(by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (a * w + b)).analyticAt z`.
-/
lemma sg_analyticAt (hb : SgStarBasic) (a b z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L (a * w + b)) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (a * w + b)).analyticAt z

/- English proof (translation)
Use `(meromorphicOrderAt_eq_int_iff (n := 0) hg.meromorphicAt).2 ⟨g, hg, h, by simp⟩` as an intermediate fact. Simplify using `using this`.
-/
private lemma meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (h : g x ≠ 0) :
    meromorphicOrderAt g x = 0 := by
  have := (meromorphicOrderAt_eq_int_iff (n := 0) hg.meromorphicAt).2 ⟨g, hg, h, by simp⟩
  simpa using this

/- English proof (translation)
Establish `hA : AnalyticAt ℂ (fun w : ℂ => wSigma L (a * w + b)) z`. Establish `hd` using `he L`. Conclude with `(by fun_prop : Differentiable ℂ fun w : ℂ => wSigma L (a * w + b)).analyticAt z`. Establish `hE : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)) z` using `(by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)).analyticAt z`. Establish `hf : (fun w : ℂ => sgStar L (a * w + b)) = (fun w : ℂ => wSigma L (a * w + b)) * fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)`.

Use function extensionality and compare the values at `w`. Both sides reduce to the same expression. Rewrite using `[hf, meromorphicOrderAt_mul hA.meromorphicAt hE.meromorphicAt, hord L a b z ha, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hE (Complex.exp_ne_zero _), add_zero]`. Both sides reduce to the same expression.
-/
lemma sg_order (hord : SigmaOrder) (he : SigmaEntire) (a b z : ℂ) (ha : a ≠ 0) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (a * w + b)) z = ind L (a * z + b) := by
  have hA : AnalyticAt ℂ (fun w : ℂ => wSigma L (a * w + b)) z := by
    have hd := he L
    exact (by fun_prop : Differentiable ℂ fun w : ℂ => wSigma L (a * w + b)).analyticAt z
  have hE : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)) z :=
    (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2)).analyticAt z
  have hf : (fun w : ℂ => sgStar L (a * w + b)) =
      (fun w : ℂ => wSigma L (a * w + b)) * fun w : ℂ => Complex.exp (-(s2 L) * (a * w + b) ^ 2 / 2) := by
    funext w; rfl
  rw [hf, meromorphicOrderAt_mul hA.meromorphicAt hE.meromorphicAt, hord L a b z ha,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hE (Complex.exp_ne_zero _), add_zero]
  rfl

variable (α : ℂ) (S : Finset ℂ)

def num (z : ℂ) : ℂ := sgStar L (α * z) ^ 2

def fac (P z : ℂ) : ℂ := (-(sgStar L P ^ 2)⁻¹) * (sgStar L (z + P) * sgStar L (z - P))

def den (z : ℂ) : ℂ := α ^ 2 * sgStar L z ^ 2 * ∏ P ∈ S, fac L P z

def mlt (ω z : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)

/- English proof (translation)
Apply the tactic sequence `unfold semiChar; split_ifs <;> norm_num`.
-/
lemma semiChar_sq (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold semiChar; split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[hq L ω z hω]`. Simplify using `only [mlt]`. Take the linear combination `(Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2 * sgStar L z ^ 2) * semiChar_sq L ω`.
-/
lemma sg_sq_add (hq : SgStarQuasi) (ω z : ℂ) (hω : ω ∈ L.lattice) :
    sgStar L (z + ω) ^ 2 = mlt L ω z ^ 2 * sgStar L z ^ 2 := by
  rw [hq L ω z hω]; simp only [mlt]
  linear_combination (Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2 *
    sgStar L z ^ 2) * semiChar_sq L ω

/- English proof (translation)
Establish `h1` using `hq L ω (z + P) hω`. Establish `h2` using `hq L ω (z - P) hω`. Establish `e1 : z + ω + P = z + P + ω` using `by ring`. Establish `e2 : z + ω - P = z - P + ω` using `by ring`. Establish `hE : Complex.exp ((Real.pi : ℂ) * herm L (z + P) ω + (Real.pi : ℂ) * herm L ω ω / 2) * Complex.exp ((Real.pi : ℂ) * herm L (z - P) ω + (Real.pi : ℂ) * herm L ω ω / 2) = Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2`.

Rewrite using `[sq, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [fac, mlt]`.

Rewrite using `[e1, e2, h1, h2]`. Take the linear combination `(-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) * semiChar L ω ^ 2) * hE + (-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2) * semiChar_sq L ω`.
-/
lemma fac_add (hq : SgStarQuasi) (P ω z : ℂ) (hω : ω ∈ L.lattice) :
    fac L P (z + ω) = mlt L ω z ^ 2 * fac L P z := by
  have h1 := hq L ω (z + P) hω
  have h2 := hq L ω (z - P) hω
  have e1 : z + ω + P = z + P + ω := by ring
  have e2 : z + ω - P = z - P + ω := by ring
  have hE : Complex.exp ((Real.pi : ℂ) * herm L (z + P) ω + (Real.pi : ℂ) * herm L ω ω / 2) *
      Complex.exp ((Real.pi : ℂ) * herm L (z - P) ω + (Real.pi : ℂ) * herm L ω ω / 2) =
      Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2 := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]; congr 1; simp only [herm]; ring
  simp only [fac, mlt]
  rw [e1, e2, h1, h2]
  linear_combination (-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) * semiChar L ω ^ 2) * hE +
    (-(sgStar L P ^ 2)⁻¹ * sgStar L (z + P) * sgStar L (z - P) *
      Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) ^ 2) * semiChar_sq L ω

/- English proof (translation)
Simplify using `only [den]`. Rewrite using `[sg_sq_add L hq ω z hω, Finset.prod_congr rfl (fun P _ => fac_add L hq P ω z hω), Finset.prod_mul_distrib, Finset.prod_const]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma den_add (hq : SgStarQuasi) (ω z : ℂ) (hω : ω ∈ L.lattice) :
    den L α S (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * den L α S z := by
  simp only [den]
  rw [sg_sq_add L hq ω z hω, Finset.prod_congr rfl (fun P _ => fac_add L hq P ω z hω),
    Finset.prod_mul_distrib, Finset.prod_const]
  ring

/- English proof (translation)
Simplify using `only [herm, map_mul]`. Rewrite using `[← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_mul (z ω : ℂ) : herm L (α * z) (α * ω) = (Complex.normSq α : ℂ) * herm L z ω := by
  simp only [herm, map_mul]; rw [← Complex.mul_conj]; ring

/- English proof (translation)
Simplify using `only [num]`. Rewrite using `[mul_add, sg_sq_add L hq (α * ω) (α * z) (hst ω hω)]`. Use `congr 1`. Establish `hN : (Complex.normSq α : ℂ) = ((S.card + 1 : ℕ) : ℂ)`. Rewrite using `[← hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ x y : ℂ, Complex.exp ((Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * x) + (Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * y) / 2) = Complex.exp ((Real.pi : ℂ) * x + (Real.pi : ℂ) * y / 2) ^ (S.card + 1)`. Introduce `x y`. Rewrite using `[← Complex.exp_nat_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mlt]`. Rewrite using `[herm_mul L α z ω, herm_mul L α ω ω, hN, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma num_add (hq : SgStarQuasi) (hst : MulStable L α) (hc : (S.card : ℝ) + 1 = Complex.normSq α)
    (ω z : ℂ) (hω : ω ∈ L.lattice) :
    num L α (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * num L α z := by
  simp only [num]
  rw [mul_add, sg_sq_add L hq (α * ω) (α * z) (hst ω hω)]
  congr 1
  have hN : (Complex.normSq α : ℂ) = ((S.card + 1 : ℕ) : ℂ) := by
    rw [← hc]; push_cast; ring
  have key : ∀ x y : ℂ, Complex.exp ((Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * x) +
      (Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * y) / 2) =
      Complex.exp ((Real.pi : ℂ) * x + (Real.pi : ℂ) * y / 2) ^ (S.card + 1) := by
    intro x y; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp only [mlt]
  rw [herm_mul L α z ω, herm_mul L α ω ω, hN, key]
  ring

/- English proof (translation)
Use `sg_order L hord he 1 P z one_ne_zero` as an intermediate fact. Simplify using `only [one_mul] at this`. Conclude with `this`.
-/
lemma sg_add_order (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (w + P)) z = ind L (z + P) := by
  have := sg_order L hord he 1 P z one_ne_zero
  simp only [one_mul] at this
  exact this

/- English proof (translation)
Use `sg_order L hord he 1 (-P) z one_ne_zero` as an intermediate fact. Simplify using `only [one_mul, ← sub_eq_add_neg] at this`. Conclude with `this`.
-/
lemma sg_sub_order (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (w - P)) z = ind L (z - P) := by
  have := sg_order L hord he 1 (-P) z one_ne_zero
  simp only [one_mul, ← sub_eq_add_neg] at this
  exact this

/- English proof (translation)
Establish `hd` using `(hb L).1`. Conclude with `(by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (w + P)).analyticAt z`.
-/
lemma sg_add_analyticAt (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L (w + P)) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (w + P)).analyticAt z

/- English proof (translation)
Establish `hd` using `(hb L).1`. Conclude with `(by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (w - P)).analyticAt z`.
-/
lemma sg_sub_analyticAt (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L (w - P)) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (w - P)).analyticAt z

/- English proof (translation)
Establish `hd` using `(hb L).1`. Conclude with `(show Differentiable ℂ (fun w => fac L P w) by simp only [fac]; fun_prop).analyticAt z`.
-/
lemma fac_analyticAt (hb : SgStarBasic) (P z : ℂ) : AnalyticAt ℂ (fac L P) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => fac L P w) by simp only [fac]; fun_prop).analyticAt z

/- English proof (translation)
Establish `hs : sgStar L P ≠ 0` using `fun h => hP (((hb L).2.2.1 P).1 h)`. Establish `h0 : AnalyticAt ℂ (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) z` using `analyticAt_const`. Establish `h1` using `sg_add_analyticAt L hb P z`. Establish `h2` using `sg_sub_analyticAt L hb P z`. Establish `h12 : AnalyticAt ℂ ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P)) z` using `h1.mul h2`.

Establish `e : fac L P = (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) * ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P))`. Use function extensionality and compare the values at `w`. Both sides reduce to the same expression. Rewrite using `[e, meromorphicOrderAt_mul h0.meromorphicAt h12.meromorphicAt, meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h0 (by simp [hs]), sg_add_order L hord he P z, sg_sub_order L hord he P z, zero_add]`.
-/
lemma fac_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (P z : ℂ)
    (hP : P ∉ L.lattice) :
    meromorphicOrderAt (fac L P) z = ind L (z + P) + ind L (z - P) := by
  have hs : sgStar L P ≠ 0 := fun h => hP (((hb L).2.2.1 P).1 h)
  have h0 : AnalyticAt ℂ (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) z := analyticAt_const
  have h1 := sg_add_analyticAt L hb P z
  have h2 := sg_sub_analyticAt L hb P z
  have h12 : AnalyticAt ℂ ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P)) z := h1.mul h2
  have e : fac L P = (fun _ : ℂ => -(sgStar L P ^ 2)⁻¹) *
      ((fun w => sgStar L (w + P)) * fun w => sgStar L (w - P)) := by
    funext w; rfl
  rw [e, meromorphicOrderAt_mul h0.meromorphicAt h12.meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt,
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h0 (by simp [hs]), sg_add_order L hord he P z, sg_sub_order L hord he P z, zero_add]

/- English proof (translation)
Use `sg_order L hord he 1 0 z one_ne_zero` as an intermediate fact. Simplify using `only [one_mul, add_zero] at this`. Conclude with `this`.
-/
lemma sg_id_order (hord : SigmaOrder) (he : SigmaEntire) (z : ℂ) :
    meromorphicOrderAt (sgStar L) z = ind L z := by
  have := sg_order L hord he 1 0 z one_ne_zero
  simp only [one_mul, add_zero] at this
  exact this

/- English proof (translation)
Establish `hd` using `(hb L).1`. Conclude with `(show Differentiable ℂ (fun w => num L α w) by simp only [num]; fun_prop).analyticAt z`.
-/
lemma num_analyticAt (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (num L α) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => num L α w) by simp only [num]; fun_prop).analyticAt z

/- English proof (translation)
Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_empty]`. Conclude with `analyticAt_const`. Introduce `a T ha ih`. Establish `e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w`.

Use function extensionality and compare the values at `w`. Rewrite using `[Finset.prod_insert ha]`. Rewrite using `[e]`. Conclude with `(fac_analyticAt L hb a z).mul ih`.
-/
private lemma analyticAt_prod_fac (hb : SgStarBasic) (T : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ P ∈ T, fac L P w) z := by
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]; exact analyticAt_const
  · intro a T ha ih
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]
    rw [e]; exact (fac_analyticAt L hb a z).mul ih

/- English proof (translation)
Establish `hd` using `(hb L).1`. Establish `h1 : AnalyticAt ℂ (fun w => α ^ 2 * sgStar L w ^ 2) z` using `(by fun_prop : Differentiable ℂ fun w => α ^ 2 * sgStar L w ^ 2).analyticAt z`. Conclude with `h1.mul (analyticAt_prod_fac L hb S z)`.
-/
lemma den_analyticAt (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (den L α S) z := by
  have hd := (hb L).1
  have h1 : AnalyticAt ℂ (fun w => α ^ 2 * sgStar L w ^ 2) z :=
    (by fun_prop : Differentiable ℂ fun w => α ^ 2 * sgStar L w ^ 2).analyticAt z
  exact h1.mul (analyticAt_prod_fac L hb S z)

/- English proof (translation)
Consider the cases of `x with`. Consider the case `top => first | rfl | decide | simp`. Consider the case `coe a`. Rewrite using `[← WithTop.coe_add, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul, two_mul]`.
-/
private lemma add_self_eq_two_mul_extended_int (x : WithTop ℤ) : x + x = 2 * x := by
  cases x with
  | top => first | rfl | decide | simp
  | coe a =>
    rw [← WithTop.coe_add, show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul,
      two_mul]

/- English proof (translation)
Establish `hd` using `(hb L).1`. Establish `hg : AnalyticAt ℂ (fun w => sgStar L (α * w)) z` using `(by fun_prop : Differentiable ℂ fun w => sgStar L (α * w)).analyticAt z`. Establish `e : num L α = (fun w => sgStar L (α * w)) * (fun w => sgStar L (α * w))`. Use function extensionality and compare the values at `w`. Conclude with `sq _`.

Rewrite using `[e, meromorphicOrderAt_mul hg.meromorphicAt hg.meromorphicAt]`. Use `sg_order L hord he α 0 z hα` as an intermediate fact. Simplify using `only [add_zero] at this`. Rewrite using `[this, add_self_eq_two_mul_extended_int]`.
-/
lemma num_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0) (z : ℂ) :
    meromorphicOrderAt (num L α) z = 2 * ind L (α * z) := by
  have hd := (hb L).1
  have hg : AnalyticAt ℂ (fun w => sgStar L (α * w)) z :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L (α * w)).analyticAt z
  have e : num L α = (fun w => sgStar L (α * w)) * (fun w => sgStar L (α * w)) := by
    funext w; exact sq _
  rw [e, meromorphicOrderAt_mul hg.meromorphicAt hg.meromorphicAt]
  have := sg_order L hord he α 0 z hα
  simp only [add_zero] at this
  rw [this, add_self_eq_two_mul_extended_int]

/- English proof (translation)
Use `revert hT`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Conclude with `meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero analyticAt_const one_ne_zero`.

Introduce `a T ha ih hT`. Establish `e : (fun w => ∏ P ∈ insert a T, fac L P w) = (fac L a) * fun w => ∏ P ∈ T, fac L P w`. Use function extensionality and compare the values at `w`. Rewrite using `[Finset.prod_insert ha]`. Both sides reduce to the same expression.

Rewrite using `[e, meromorphicOrderAt_mul (fac_analyticAt L hb a z).meromorphicAt (analyticAt_prod_fac L hb T z).meromorphicAt, fac_order L hord he hb a z (hT a (Finset.mem_insert_self a T)), ih (fun P hP => hT P (Finset.mem_insert_of_mem hP)), Finset.sum_insert ha]`.
-/
private lemma meromorphicOrderAt_prod_fac (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (T : Finset ℂ) (hT : ∀ P ∈ T, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (fun w => ∏ P ∈ T, fac L P w) z = ∑ P ∈ T, (ind L (z + P) + ind L (z - P)) := by
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero analyticAt_const one_ne_zero
  · intro a T ha ih hT
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = (fac L a) * fun w => ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]; rfl
    rw [e, meromorphicOrderAt_mul (fac_analyticAt L hb a z).meromorphicAt
      (analyticAt_prod_fac L hb T z).meromorphicAt,
      fac_order L hord he hb a z (hT a (Finset.mem_insert_self a T)),
      ih (fun P hP => hT P (Finset.mem_insert_of_mem hP)), Finset.sum_insert ha]

/- English proof (translation)
Establish `hd` using `(hb L).1`. Establish `h1 : AnalyticAt ℂ (fun _ : ℂ => α ^ 2) z` using `analyticAt_const`. Establish `h2 : AnalyticAt ℂ (fun w => sgStar L w ^ 2) z` using `(by fun_prop : Differentiable ℂ fun w => sgStar L w ^ 2).analyticAt z`. Establish `h12 : AnalyticAt ℂ ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) z` using `h1.mul h2`. Establish `e : den L α S = ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) * fun w => ∏ P ∈ S, fac L P w`.

Use function extensionality and compare the values at `w`. Both sides reduce to the same expression. Establish `hs : (fun w => sgStar L w ^ 2) = sgStar L * sgStar L`. Use function extensionality and compare the values at `w`. Conclude with `sq _`.

Establish `hm : MeromorphicAt (sgStar L) z` using `(hd.analyticAt z).meromorphicAt`. Rewrite using `[e, meromorphicOrderAt_mul h12.meromorphicAt (analyticAt_prod_fac L hb S z).meromorphicAt, meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h1 (pow_ne_zero 2 hα), meromorphicOrderAt_prod_fac L hord he hb S hS z, zero_add, …`.
-/
lemma den_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : ∀ P ∈ S, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (den L α S) z
      = 2 * ind L z + ∑ P ∈ S, (ind L (z + P) + ind L (z - P)) := by
  have hd := (hb L).1
  have h1 : AnalyticAt ℂ (fun _ : ℂ => α ^ 2) z := analyticAt_const
  have h2 : AnalyticAt ℂ (fun w => sgStar L w ^ 2) z :=
    (by fun_prop : Differentiable ℂ fun w => sgStar L w ^ 2).analyticAt z
  have h12 : AnalyticAt ℂ ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) z := h1.mul h2
  have e : den L α S = ((fun _ : ℂ => α ^ 2) * fun w => sgStar L w ^ 2) * fun w => ∏ P ∈ S, fac L P w := by
    funext w; rfl
  have hs : (fun w => sgStar L w ^ 2) = sgStar L * sgStar L := by
    funext w; exact sq _
  have hm : MeromorphicAt (sgStar L) z := (hd.analyticAt z).meromorphicAt
  rw [e, meromorphicOrderAt_mul h12.meromorphicAt (analyticAt_prod_fac L hb S z).meromorphicAt,
    meromorphicOrderAt_mul h1.meromorphicAt h2.meromorphicAt, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero h1 (pow_ne_zero 2 hα),
    meromorphicOrderAt_prod_fac L hord he hb S hS z, zero_add, hs, meromorphicOrderAt_mul hm hm,
    sg_id_order L hord he z, add_self_eq_two_mul_extended_int]

/- English proof (translation)
Take `⟨P0, hP0, hz⟩` from `hS.2.2 z h1 h2`. Rewrite using `[Finset.sum_eq_single P0]`. Conclude with `ind_of_mem L hz`. Introduce `b hb hne`. Apply `ind_of_notMem L` to reduce the goal to its premises.

Introduce `hb'`. Apply `hne` to reduce the goal to its premises. Apply `hS.2.1 b hb P0 hP0` to reduce the goal to its premises. Establish `e : b - P0 = (z - P0) - (z - b)` using `by ring`. Rewrite using `[e]`.

Conclude with `L.lattice.sub_mem hz hb'`. Introduce `h`. Conclude with `absurd hP0 h`.
-/
lemma count_sub (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) (h2 : z ∉ L.lattice) :
    ∑ P ∈ S, ind L (z - P) = 1 := by
  obtain ⟨P0, hP0, hz⟩ := hS.2.2 z h1 h2
  rw [Finset.sum_eq_single P0]
  · exact ind_of_mem L hz
  · intro b hb hne
    apply ind_of_notMem L
    intro hb'
    apply hne
    apply hS.2.1 b hb P0 hP0
    have e : b - P0 = (z - P0) - (z - b) := by ring
    rw [e]; exact L.lattice.sub_mem hz hb'
  · intro h; exact absurd hP0 h

/- English proof (translation)
Establish `hn1 : α * -z ∈ L.lattice` using `by rw [mul_neg]; exact L.lattice.neg_mem h1`. Establish `hn2 : -z ∉ L.lattice` using `fun h => h2 (by simpa using L.lattice.neg_mem h)`. Take `⟨P0, hP0, hz⟩` from `hS.2.2 (-z) hn1 hn2`. Establish `hz' : z + P0 ∈ L.lattice`. Use `L.lattice.neg_mem hz` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_eq_single P0]`. Conclude with `ind_of_mem L hz'`. Introduce `b hb hne`.

Apply `ind_of_notMem L` to reduce the goal to its premises. Introduce `hb'`. Apply `hne` to reduce the goal to its premises. Apply `hS.2.1 b hb P0 hP0` to reduce the goal to its premises. Establish `e : b - P0 = (z + b) - (z + P0)` using `by ring`.

Rewrite using `[e]`. Conclude with `L.lattice.sub_mem hb' hz'`. Introduce `h`. Conclude with `absurd hP0 h`.
-/
lemma count_add (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) (h2 : z ∉ L.lattice) :
    ∑ P ∈ S, ind L (z + P) = 1 := by
  have hn1 : α * -z ∈ L.lattice := by rw [mul_neg]; exact L.lattice.neg_mem h1
  have hn2 : -z ∉ L.lattice := fun h => h2 (by simpa using L.lattice.neg_mem h)
  obtain ⟨P0, hP0, hz⟩ := hS.2.2 (-z) hn1 hn2
  have hz' : z + P0 ∈ L.lattice := by
    have := L.lattice.neg_mem hz
    convert this using 1; ring
  rw [Finset.sum_eq_single P0]
  · exact ind_of_mem L hz'
  · intro b hb hne
    apply ind_of_notMem L
    intro hb'
    apply hne
    apply hS.2.1 b hb P0 hP0
    have e : b - P0 = (z + b) - (z + P0) := by ring
    rw [e]; exact L.lattice.sub_mem hb' hz'
  · intro h; exact absurd hP0 h

/- English proof (translation)
Rewrite using `[den_order L α S hord he hb hα (fun P hP => (hS.1 P hP).2) z]`. Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[ind_of_mem L hz]`. Establish `h0 : ∀ P ∈ S, ind L (z + P) + ind L (z - P) = 0`. Introduce `P hP`.

Establish `hPL` using `(hS.1 P hP).2`. Rewrite using `[ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem h hz)), ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem hz h))]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl h0, Finset.sum_const_zero]`. Both sides reduce to the same expression.

Rewrite using `[ind_of_notMem L hz, Finset.sum_add_distrib, count_add L α S hS z h1 hz, count_sub L α S hS z h1 hz]`. Both sides reduce to the same expression.
-/
lemma den_order_two (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : IsKerReps L α S) (z : ℂ) (h1 : α * z ∈ L.lattice) :
    meromorphicOrderAt (den L α S) z = 2 := by
  rw [den_order L α S hord he hb hα (fun P hP => (hS.1 P hP).2) z]
  by_cases hz : z ∈ L.lattice
  · rw [ind_of_mem L hz]
    have h0 : ∀ P ∈ S, ind L (z + P) + ind L (z - P) = 0 := by
      intro P hP
      have hPL := (hS.1 P hP).2
      rw [ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem h hz)),
        ind_of_notMem L (fun h => hPL (by simpa using L.lattice.sub_mem hz h))]
      simp
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    rfl
  · rw [ind_of_notMem L hz, Finset.sum_add_distrib, count_add L α S hS z h1 hz, count_sub L α S hS z h1 hz]
    rfl

/- English proof (translation)
Establish `hz` using `(hb L).2.2.1`. Unfold `den at h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd ((pow_eq_zero_iff two_ne_zero).1 h) hα`.

Conclude with `hst z ((hz z).1 ((pow_eq_zero_iff two_ne_zero).1 h))`. Take `⟨P, hP, h⟩` from `Finset.prod_eq_zero_iff.1 h`. Establish `hPL` using `hS.1 P hP`. Establish `hs : sgStar L P ≠ 0` using `fun h0 => hPL.2 ((hz P).1 h0)`. Unfold `fac at h`.

Break down `mul_eq_zero.1 h with h | h` into its components or cases. It suffices to derive a contradiction. Simplify using `[hs] at h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Establish `h3` using `hst _ ((hz _).1 h)`.

Establish `e : α * z = α * (z + P) - α * P` using `by ring`. Rewrite using `[e]`. Conclude with `L.lattice.sub_mem h3 hPL.1`. Establish `h3` using `hst _ ((hz _).1 h)`. Establish `e : α * z = α * (z - P) + α * P` using `by ring`.

Rewrite using `[e]`. Conclude with `L.lattice.add_mem h3 hPL.1`.
-/
lemma mem_of_den_eq_zero (hb : SgStarBasic) (hα : α ≠ 0) (hst : MulStable L α)
    (hS : IsKerReps L α S) (z : ℂ) (h : den L α S z = 0) : α * z ∈ L.lattice := by
  have hz := (hb L).2.2.1
  unfold den at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hα
    · exact hst z ((hz z).1 ((pow_eq_zero_iff two_ne_zero).1 h))
  · obtain ⟨P, hP, h⟩ := Finset.prod_eq_zero_iff.1 h
    have hPL := hS.1 P hP
    have hs : sgStar L P ≠ 0 := fun h0 => hPL.2 ((hz P).1 h0)
    unfold fac at h
    rcases mul_eq_zero.1 h with h | h
    · exfalso; simp [hs] at h
    · rcases mul_eq_zero.1 h with h | h
      · have h3 := hst _ ((hz _).1 h)
        have e : α * z = α * (z + P) - α * P := by ring
        rw [e]; exact L.lattice.sub_mem h3 hPL.1
      · have h3 := hst _ ((hz _).1 h)
        have e : α * z = α * (z - P) + α * P := by ring
        rw [e]; exact L.lattice.add_mem h3 hPL.1

/- English proof (translation)
Establish `hnum` using `num_analyticAt L α hb z`. Establish `hden` using `den_analyticAt L α S hb z`. Establish `e : (fun w => num L α w / den L α S w) = num L α * (den L α S)⁻¹`. Use function extensionality and compare the values at `w`. Conclude with `div_eq_mul_inv _ _`.

Rewrite using `[e, meromorphicOrderAt_mul hnum.meromorphicAt hden.meromorphicAt.inv, meromorphicOrderAt_inv, num_order L α hord he hb hα z]`. Distinguish the cases in `h : α * z ∈ L.lattice`. Rewrite using `[den_order_two L α S hord he hb hα hS z h, ind_of_mem L h]`. Evaluate the decidable proposition. Rewrite using `[meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hden (fun h0 => h (mem_of_den_eq_zero L α S hb hα hst hS z h0)), ind_of_notMem L h]`.

Evaluate the decidable proposition.
-/
lemma quot_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) :
    0 ≤ meromorphicOrderAt (fun w => num L α w / den L α S w) z := by
  have hnum := num_analyticAt L α hb z
  have hden := den_analyticAt L α S hb z
  have e : (fun w => num L α w / den L α S w) = num L α * (den L α S)⁻¹ := by
    funext w; exact div_eq_mul_inv _ _
  rw [e, meromorphicOrderAt_mul hnum.meromorphicAt hden.meromorphicAt.inv, meromorphicOrderAt_inv,
    num_order L α hord he hb hα z]
  by_cases h : α * z ∈ L.lattice
  · rw [den_order_two L α S hord he hb hα hS z h, ind_of_mem L h]
    decide
  · rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hden (fun h0 => h (mem_of_den_eq_zero L α S hb hα hst hS z h0)), ind_of_notMem L h]
    decide

/- English proof (translation)
Introduce `ω hω z`. Use `show num L α (z + ω) / den L α S (z + ω) = num L α z / den L α S z`. Rewrite using `[num_add L α S hq hst hc ω z hω, den_add L α S hq ω z hω]`. Conclude with `mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ (by simp only [mlt]; exact Complex.exp_ne_zero _)))`.
-/
lemma quot_periodic (hq : SgStarQuasi) (hst : MulStable L α)
    (hc : (S.card : ℝ) + 1 = Complex.normSq α) :
    IsPeriodic L (fun w => num L α w / den L α S w) := by
  intro ω hω z
  show num L α (z + ω) / den L α S (z + ω) = num L α z / den L α S z
  rw [num_add L α S hq hst hc ω z hω, den_add L α S hq ω z hω]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ (by simp only [mlt]; exact Complex.exp_ne_zero _)))

/- English proof (translation)
Establish `hmer : ∀ z, MeromorphicAt (fun w => num L α w / den L α S w) z` using `fun z => (num_analyticAt L α hb z).meromorphicAt.div (den_analyticAt L α S hb z).meromorphicAt`. Take `⟨c, hc'⟩` from `hN L _ hmer (quot_periodic L α S hq hst hc) (quot_order L α S hord he hb hα hst hS)`. Use `⟨c, fun z => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : den L α S z = 0`. Rewrite using `[h0, mul_zero]`.

Establish `hm` using `mem_of_den_eq_zero L α S hb hα hst hS z h0`. Simplify using `[num, ((hb L).2.2.1 _).2 hm]`. Establish `hcont : ContinuousAt (fun w => num L α w / den L α S w) z` using `(num_analyticAt L α hb z).continuousAt.div (den_analyticAt L α S hb z).continuousAt h0`. Conclude with `(div_eq_iff h0).1 (hc' z hcont)`.
-/
lemma exists_const (hN : EllipticNoPole) (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic)
    (hq : SgStarQuasi) (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S)
    (hc : (S.card : ℝ) + 1 = Complex.normSq α) :
    ∃ c : ℂ, ∀ z, num L α z = c * den L α S z := by
  have hmer : ∀ z, MeromorphicAt (fun w => num L α w / den L α S w) z := fun z =>
    (num_analyticAt L α hb z).meromorphicAt.div (den_analyticAt L α S hb z).meromorphicAt
  obtain ⟨c, hc'⟩ := hN L _ hmer (quot_periodic L α S hq hst hc) (quot_order L α S hord he hb hα hst hS)
  refine ⟨c, fun z => ?_⟩
  by_cases h0 : den L α S z = 0
  · rw [h0, mul_zero]
    have hm := mem_of_den_eq_zero L α S hb hα hst hS z h0
    simp [num, ((hb L).2.2.1 _).2 hm]
  · have hcont : ContinuousAt (fun w => num L α w / den L α S w) z :=
      (num_analyticAt L α hb z).continuousAt.div (den_analyticAt L α S hb z).continuousAt h0
    exact (div_eq_iff h0).1 (hc' z hcont)

/- English proof (translation)
Establish `h` using `sub_smul_dslope (sgStar L) 0 z`. Simplify using `only [sub_zero, smul_eq_mul] at h`. Rewrite using `[h, ((hb L).2.2.1 0).2 L.lattice.zero_mem, sub_zero]`.
-/
lemma sg_eq_mul_dslope (hb : SgStarBasic) (z : ℂ) : sgStar L z = z * dslope (sgStar L) 0 z := by
  have h := sub_smul_dslope (sgStar L) 0 z
  simp only [sub_zero, smul_eq_mul] at h
  rw [h, ((hb L).2.2.1 0).2 L.lattice.zero_mem, sub_zero]

/- English proof (translation)
Establish `hs : sgStar L P ≠ 0` using `fun h0 => hP (((hb L).2.2.1 P).1 h0)`. Simplify using `only [fac, zero_add, zero_sub, (hb L).2.1]`. Establish `e : -(sgStar L P ^ 2)⁻¹ * (sgStar L P * -sgStar L P) = (sgStar L P ^ 2)⁻¹ * sgStar L P ^ 2` using `by ring`. Rewrite using `[e, inv_mul_cancel₀ (pow_ne_zero 2 hs)]`.
-/
lemma fac_zero (hb : SgStarBasic) (P : ℂ) (hP : P ∉ L.lattice) : fac L P 0 = 1 := by
  have hs : sgStar L P ≠ 0 := fun h0 => hP (((hb L).2.2.1 P).1 h0)
  simp only [fac, zero_add, zero_sub, (hb L).2.1]
  have e : -(sgStar L P ^ 2)⁻¹ * (sgStar L P * -sgStar L P) = (sgStar L P ^ 2)⁻¹ * sgStar L P ^ 2 := by ring
  rw [e, inv_mul_cancel₀ (pow_ne_zero 2 hs)]

/- English proof (translation)
Establish `hdiff : DifferentiableAt ℂ (sgStar L) 0` using `(hb L).1 0`. Establish `hdc : ContinuousAt (dslope (sgStar L) 0) 0` using `continuousAt_dslope_same.2 hdiff`. Establish `hd0 : dslope (sgStar L) 0 0 = 1` using `by rw [dslope_same]; exact (hb L).2.2.2.1`. Establish `g1c : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w) ^ 2) 0`. Establish `h1 : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w)) 0` using `ContinuousAt.comp_of_eq hdc (by fun_prop) (by simp)`.

Conclude with `h1.pow 2`. Establish `hprod : ContinuousAt (fun w => ∏ P ∈ S, fac L P w) 0` using `(analyticAt_prod_fac L hb S 0).continuousAt`. Establish `g2c : ContinuousAt (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) 0` using `(continuousAt_const.mul (hdc.pow 2)).mul hprod`. Establish `heq : (fun w => dslope (sgStar L) 0 (α * w) ^ 2) =ᶠ[𝓝[≠] 0] (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w)` using `by filter_upwards [self_mem_nhdsWithin] with w hw`. Establish `hw' : w ≠ 0` using `hw`.

Establish `hh` using `h w`. Simplify using `only [num, den] at hh`. Rewrite `hh` using `[sg_eq_mul_dslope L hb (α * w), sg_eq_mul_dslope L hb w]`. Establish `hne : α ^ 2 * w ^ 2 ≠ 0` using `mul_ne_zero (pow_ne_zero 2 hα) (pow_ne_zero 2 hw')`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises.

Take the linear combination `hh`. Establish `key` using `tendsto_nhds_unique (g1c.tendsto.mono_left nhdsWithin_le_nhds) ((g2c.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)`. Simplify using `only [mul_zero, hd0, one_pow, mul_one] at key`. Rewrite `key` using `[Finset.prod_congr rfl (fun P hP => fac_zero L hb P (hS P hP)), Finset.prod_const_one, mul_one]`. Conclude with `key.symm`.
-/
lemma const_eq_one (hb : SgStarBasic) (hα : α ≠ 0) (hS : ∀ P ∈ S, P ∉ L.lattice) (c : ℂ)
    (h : ∀ z, num L α z = c * den L α S z) : c = 1 := by
  have hdiff : DifferentiableAt ℂ (sgStar L) 0 := (hb L).1 0
  have hdc : ContinuousAt (dslope (sgStar L) 0) 0 := continuousAt_dslope_same.2 hdiff
  have hd0 : dslope (sgStar L) 0 0 = 1 := by rw [dslope_same]; exact (hb L).2.2.2.1
  have g1c : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w) ^ 2) 0 := by
    have h1 : ContinuousAt (fun w => dslope (sgStar L) 0 (α * w)) 0 :=
      ContinuousAt.comp_of_eq hdc (by fun_prop) (by simp)
    exact h1.pow 2
  have hprod : ContinuousAt (fun w => ∏ P ∈ S, fac L P w) 0 := (analyticAt_prod_fac L hb S 0).continuousAt
  have g2c : ContinuousAt (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) 0 :=
    (continuousAt_const.mul (hdc.pow 2)).mul hprod
  have heq : (fun w => dslope (sgStar L) 0 (α * w) ^ 2) =ᶠ[𝓝[≠] 0]
      (fun w => c * dslope (sgStar L) 0 w ^ 2 * ∏ P ∈ S, fac L P w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ≠ 0 := hw
    have hh := h w
    simp only [num, den] at hh
    rw [sg_eq_mul_dslope L hb (α * w), sg_eq_mul_dslope L hb w] at hh
    have hne : α ^ 2 * w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hα) (pow_ne_zero 2 hw')
    apply mul_left_cancel₀ hne
    linear_combination hh
  have key := tendsto_nhds_unique (g1c.tendsto.mono_left nhdsWithin_le_nhds)
    ((g2c.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  simp only [mul_zero, hd0, one_pow, mul_one] at key
  rw [Finset.prod_congr rfl (fun P hP => fac_zero L hb P (hS P hP)), Finset.prod_const_one, mul_one] at key
  exact key.symm

/- English proof (translation)
Establish `hs : sgStar L P ^ 2 ≠ 0` using `pow_ne_zero 2 (fun h0 => hP (((hb L).2.2.1 P).1 h0))`. Simplify using `only [fac]`. Rewrite using `[hsa L z P hz hP]`. Use `inv_mul_cancel₀ hs` as an intermediate fact. Take the linear combination `(sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P)) * this`.
-/
lemma fac_eq (hb : SgStarBasic) (hsa : SgStarAdd) (P z : ℂ) (hP : P ∉ L.lattice)
    (hz : z ∉ L.lattice) :
    fac L P z = sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P) := by
  have hs : sgStar L P ^ 2 ≠ 0 := pow_ne_zero 2 (fun h0 => hP (((hb L).2.2.1 P).1 h0))
  simp only [fac]
  rw [hsa L z P hz hP]
  have := inv_mul_cancel₀ hs
  linear_combination (sgStar L z ^ 2 * (L.weierstrassP z - L.weierstrassP P)) * this

end IsogenySigmaQuotient

open IsogenySigmaQuotient in
/- English proof (translation)
Introduce `L α S hα hst hS z hz`. Establish `hc` using `hcard L α S hα hst hS`. Establish `hS' : ∀ P ∈ S, P ∉ L.lattice` using `fun P hP => (hS.1 P hP).2`. Take `⟨c, hc'⟩` from `exists_const L α S hN hord he hb hq hα hst hS hc`. Establish `h1` using `const_eq_one L α S hb hα hS' c hc'`.

Substitute `h1` using the available equality. Establish `h` using `hc' z`. Simplify using `only [num, den, one_mul] at h`. Rewrite using `[h, Finset.prod_congr rfl (fun P hP => fac_eq L hb hsa P z (hS' P hP) hz), Finset.prod_mul_distrib, Finset.prod_const]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isogenySigma_of (hN : EllipticNoPole) (hord : SigmaOrder) (hsa : SgStarAdd)
    (hq : SgStarQuasi) (hb : SgStarBasic) (hcard : KerRepsCard) (he : SigmaEntire) :
    IsogenySigma := by
  intro L α S hα hst hS z hz
  have hc := hcard L α S hα hst hS
  have hS' : ∀ P ∈ S, P ∉ L.lattice := fun P hP => (hS.1 P hP).2
  obtain ⟨c, hc'⟩ := exists_const L α S hN hord he hb hq hα hst hS hc
  have h1 := const_eq_one L α S hb hα hS' c hc'
  subst h1
  have h := hc' z
  simp only [num, den, one_mul] at h
  rw [h, Finset.prod_congr rfl (fun P hP => fac_eq L hb hsa P z (hS' P hP) hz), Finset.prod_mul_distrib,
    Finset.prod_const]
  ring

end Formalism.L2.Th1.F
