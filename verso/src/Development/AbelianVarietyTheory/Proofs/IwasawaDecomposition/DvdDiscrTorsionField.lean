import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionRam

open WeierstrassCurve WeierstrassCurve.Affine

section Local

variable {k : Type} [Field k] (V : ValuationSubring k)

/- English proof (translation)
Break down `V.mem_or_inv_mem x with hx | hx` into its components or cases. Conclude with `hx`. Distinguish the cases in `h0 : x = 0`. Conclude with `h0 ▸ V.zero_mem`. Establish `: x = -(c⁻¹ * (a + b * x⁻¹ + e * x⁻¹ ^ 2 + f * x⁻¹ ^ 3))`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Rewrite using `[this]`. Conclude with `neg_mem (mul_mem hc (add_mem (add_mem (add_mem ha (mul_mem hb hx)) (mul_mem he (pow_mem hx _))) (mul_mem hf (pow_mem hx _))))`.
-/
theorem mem_of_quartic {c a b e f x : k} (hc0 : c ≠ 0) (hc : c⁻¹ ∈ V) (ha : a ∈ V) (hb : b ∈ V) (he : e ∈ V)
    (hf : f ∈ V) (h : c * x ^ 4 + a * x ^ 3 + b * x ^ 2 + e * x + f = 0) : x ∈ V := by
  rcases V.mem_or_inv_mem x with hx | hx
  · exact hx
  by_cases h0 : x = 0
  · exact h0 ▸ V.zero_mem
  have : x = -(c⁻¹ * (a + b * x⁻¹ + e * x⁻¹ ^ 2 + f * x⁻¹ ^ 3)) := by
    field_simp
    linear_combination h
  rw [this]
  exact neg_mem (mul_mem hc (add_mem (add_mem (add_mem ha (mul_mem hb hx)) (mul_mem he (pow_mem hx _)))
    (mul_mem hf (pow_mem hx _))))

variable [DecidableEq k] {V} (W : WeierstrassCurve V)

/- English proof (translation)
Establish `he` using `(equation_iff _ _).1 h.1`. Establish `c2 : ((2 : V) : k) = 2` using `rfl`. Establish `c4 : ((4 : V) : k) = 4` using `rfl`. Establish `m2 : (2 : k) ∈ V` using `(2 : V).2`. Establish `m4 : (4 : k) ∈ V` using `(4 : V).2`.

Simplify using `only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he`. Establish `hy : y ≠ (W.map V.subtype).toAffine.negY x y`. Introduce `hy`. Simplify using `only [negY, map_a₁, map_a₃, ValuationSubring.coe_subtype] at hy`. Use `hx (mem_of_quartic V (c := 4) (by rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20) (by rw [show (4 : k) = 2 * 2 by norm_num, mul_inv]; exact mul_mem h2 h2) W.b₂.2 (mul_mem m2 W.b₄.2) W.b₆.2 V.zero_mem ?_)` and prove the remaining obligations.

Simplify using `only [b₂, b₄, b₆]`. Move the coercions through the operations in `[c2, c4]`. Take the linear combination `x * (2 * y + W.a₁ * x + W.a₃) * hy - 4 * x * he`. Establish `hl` using `slope_of_Y_ne (W := (W.map V.subtype).toAffine) rfl hy`. Rewrite `hl` using `[eq_div_iff (sub_ne_zero.2 hy)]`.

Establish `key : (W.map V.subtype).toAffine.addX x x ((W.map V.subtype).toAffine.slope x x y y) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈`. Generalize the expression as in `(W.map V.subtype).toAffine.slope x x y y = l at hl`. Simplify using `only [negY, addX, map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.coe_subtype, b₂, b₄, b₆, b₈] at hl ⊢`. Move the coercions through the operations in `[c2, c4]`. Take the linear combination `(l * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) - 4 * (l ^ 2 + W.a₁ * l - W.a₂ - x - x)) * he`.

Use `⟨_, _, _, Point.add_self_of_Y_ne hy, fun hm => hx ?_, key⟩` and prove the remaining obligations. Use `mem_of_quartic V (c := 1) one_ne_zero (by simp) (neg_mem (mul_mem m4 hm)) (neg_mem (add_mem W.b₄.2 (mul_mem hm W.b₂.2))) (neg_mem (mul_mem m2 (add_mem W.b₆.2 (mul_mem hm W.b₄.2)))) (neg_mem (add_mem W.b₈.2 (mul_mem hm W.b₆.2))) ?_` and prove the remaining obligations. Take the linear combination `-key`.
-/
theorem double_not_mem (h20 : (2 : k) ≠ 0) (h2 : (2 : k)⁻¹ ∈ V) {x y : k}
    (h : (W.map V.subtype).toAffine.Nonsingular x y) (hx : x ∉ V) :
    ∃ x' y' h', Point.some x y h + Point.some x y h = Point.some x' y' h' ∧ x' ∉ V ∧
      x' * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have he := (equation_iff _ _).1 h.1
  have c2 : ((2 : V) : k) = 2 := rfl
  have c4 : ((4 : V) : k) = 4 := rfl
  have m2 : (2 : k) ∈ V := (2 : V).2
  have m4 : (4 : k) ∈ V := (4 : V).2
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he
  have hy : y ≠ (W.map V.subtype).toAffine.negY x y := by
    intro hy
    simp only [negY, map_a₁, map_a₃, ValuationSubring.coe_subtype] at hy
    refine hx (mem_of_quartic V (c := 4) (by rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20)
      (by rw [show (4 : k) = 2 * 2 by norm_num, mul_inv]; exact mul_mem h2 h2) W.b₂.2 (mul_mem m2 W.b₄.2) W.b₆.2
      V.zero_mem ?_)
    simp only [b₂, b₄, b₆]
    push_cast [c2, c4]
    linear_combination x * (2 * y + W.a₁ * x + W.a₃) * hy - 4 * x * he
  have hl := slope_of_Y_ne (W := (W.map V.subtype).toAffine) rfl hy
  rw [eq_div_iff (sub_ne_zero.2 hy)] at hl
  have key : (W.map V.subtype).toAffine.addX x x ((W.map V.subtype).toAffine.slope x x y y) *
      (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    generalize (W.map V.subtype).toAffine.slope x x y y = l at hl
    simp only [negY, addX, map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.coe_subtype, b₂, b₄, b₆, b₈] at hl ⊢
    push_cast [c2, c4]
    linear_combination (l * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
      W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl +
      (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) - 4 * (l ^ 2 + W.a₁ * l - W.a₂ - x - x)) * he
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, fun hm => hx ?_, key⟩
  refine mem_of_quartic V (c := 1) one_ne_zero (by simp) (neg_mem (mul_mem m4 hm))
    (neg_mem (add_mem W.b₄.2 (mul_mem hm W.b₂.2))) (neg_mem (mul_mem m2 (add_mem W.b₆.2 (mul_mem hm W.b₄.2))))
    (neg_mem (add_mem W.b₈.2 (mul_mem hm W.b₆.2))) ?_
  linear_combination -key

/- English proof (translation)
Establish `hx : x ∈ V`. Assume the negation of the conclusion as `hx`. Take `⟨x₂, y₂, h₂, e₂, n₂, -⟩` from `double_not_mem W h20 h2 h hx`. Take `⟨x₄, y₄, h₄, e₄, n₄, -⟩` from `double_not_mem W h20 h2 h₂ n₂`. Take `⟨x₈, y₈, h₈, e₈, n₈, key⟩` from `double_not_mem W h20 h2 h₄ n₄`.

Establish `e : Point.some x₈ y₈ h₈ = -Point.some x₄ y₄ h₄`. Rewrite using `[eq_neg_iff_add_eq_zero, ← e₈, ← e₄, ← e₂, ← h12]`. Normalize the expressions using the abelian group laws. Rewrite `e` using `[Point.neg_some, Point.some.injEq]`. Establish `m3 : (3 : k) ∈ V` using `(3 : V).2`.

Use `n₄ (mem_of_quartic V h30 h3 W.b₂.2 (mul_mem m3 W.b₄.2) (mul_mem m3 W.b₆.2) W.b₈.2 ?_)` and prove the remaining obligations. Rewrite `key` using `[e.1]`. Take the linear combination `key`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `he` using `(equation_iff _ _).1 h.1`.

Simplify using `only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he`. Use `mem_of_quartic V (c := 1) one_ne_zero (by simp) (add_mem (mul_mem W.a₁.2 hx) W.a₃.2) (neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem W.a₂.2 (pow_mem hx 2))) (mul_mem W.a₄.2 hx)) W.a₆.2)) V.zero_mem V.zero_mem ?_` and prove the remaining obligations. Take the linear combination `y ^ 2 * he`.
-/
theorem torsion_mem (h20 : (2 : k) ≠ 0) (h2 : (2 : k)⁻¹ ∈ V) (h30 : (3 : k) ≠ 0) (h3 : (3 : k)⁻¹ ∈ V) {x y : k}
    (h : (W.map V.subtype).toAffine.Nonsingular x y) (h12 : 12 • Point.some x y h = 0) : x ∈ V ∧ y ∈ V := by
  have hx : x ∈ V := by
    by_contra hx
    obtain ⟨x₂, y₂, h₂, e₂, n₂, -⟩ := double_not_mem W h20 h2 h hx
    obtain ⟨x₄, y₄, h₄, e₄, n₄, -⟩ := double_not_mem W h20 h2 h₂ n₂
    obtain ⟨x₈, y₈, h₈, e₈, n₈, key⟩ := double_not_mem W h20 h2 h₄ n₄
    have e : Point.some x₈ y₈ h₈ = -Point.some x₄ y₄ h₄ := by
      rw [eq_neg_iff_add_eq_zero, ← e₈, ← e₄, ← e₂, ← h12]
      abel
    rw [Point.neg_some, Point.some.injEq] at e
    have m3 : (3 : k) ∈ V := (3 : V).2
    refine n₄ (mem_of_quartic V h30 h3 W.b₂.2 (mul_mem m3 W.b₄.2) (mul_mem m3 W.b₆.2) W.b₈.2 ?_)
    rw [e.1] at key
    linear_combination key
  refine ⟨hx, ?_⟩
  have he := (equation_iff _ _).1 h.1
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he
  refine mem_of_quartic V (c := 1) one_ne_zero (by simp) (add_mem (mul_mem W.a₁.2 hx) W.a₃.2)
    (neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem W.a₂.2 (pow_mem hx 2))) (mul_mem W.a₄.2 hx)) W.a₆.2))
    V.zero_mem V.zero_mem ?_
  linear_combination y ^ 2 * he

open IsLocalRing in

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨mx, my⟩` from `torsion_mem W h20 h2 h30 h3 h h12`. Take `⟨mx', my'⟩` from `torsion_mem W h20 h2 h30 h3 h' h12'`. Establish `hxy : ¬(x = x' ∧ y = (W.map V.subtype).toAffine.negY x' ((W.map V.subtype).toAffine.negY x' y'))`. Rewrite using `[negY_negY]` and apply the resulting hypothesis.

Establish `hd : 12 • (Point.some x y h + -Point.some x' y' h') = 0`. Rewrite using `[smul_add, smul_neg, h12, h12', neg_zero, add_zero]`. Rewrite `hd` using `[Point.neg_some, Point.add_some hxy]`. Establish `m3` using `(torsion_mem W h20 h2 h30 h3 _ hd).1`. Establish `he` using `(equation_iff _ _).1 h.1`.

Establish `he'` using `(equation_iff _ _).1 h'.1`. Establish `hl : (W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') * (x - x') = y + y' + W.a₁ * x' + W.a₃ ∧ (W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') * (y - y') = x ^ 2 + x * x' + x' ^ 2 + W.a₂ * (x + x') + W.a₄ - W.a₁ * y`. Distinguish the cases in `hxx : x = x'`. Establish `h1` using `fun e => hxy ⟨hxx, e⟩`. Establish `h4` using `Y_eq_of_Y_ne h.1 ((equation_neg _ _).2 h'.1) hxx h1`.

Establish `h5` using `slope_of_Y_ne hxx h1`. Establish `h6 : (W.map V.subtype).toAffine.negY x y = y'` using `by rw [hxx, h4, negY_negY]`. Rewrite `h5` using `[h6, eq_div_iff (sub_ne_zero.2 fun e => hne ⟨hxx, e⟩)]`. Rewrite using `[h5]`. Substitute `hxx` using the available equality.

Simplify using `only [negY, map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.coe_subtype] at h4 ⊢`. Conclude with `⟨by linear_combination -h4, by ring⟩`. Establish `h0` using `sub_ne_zero.2 hxx`. Rewrite using `[slope_of_X_ne hxx]`. Simplify using `only [negY, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he he' ⊢`.

Prove the components needed by the constructor for the conclusion. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Take the linear combination `he - he'`.

Generalize the expression as in `(W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') = l at hl m3`. Simplify using `only [addX, map_a₁, map_a₂, ValuationSubring.coe_subtype] at m3`. Establish `ml : l ∈ V`. Use `mem_of_quartic V (c := 1) one_ne_zero (by simp) W.a₁.2 (neg_mem (add_mem (add_mem (add_mem m3 W.a₂.2) mx) mx')) V.zero_mem V.zero_mem ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `lift x to V using mx`. Use `lift y to V using my`. Use `lift x' to V using mx'`. Use `lift y' to V using my'`. Use `lift l to V using ml`.

Establish `e1 : l * (x - x') = y + y' + W.a₁ * x' + W.a₃` using `by exact_mod_cast hl.1`. Establish `e2 : l * (y - y') = x ^ 2 + x * x' + x' ^ 2 + W.a₂ * (x + x') + W.a₄ - W.a₁ * y` using `by exact_mod_cast hl.2`. Establish `e3 : residue V (x - x') = 0` using `(residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hx)`. Establish `e4 : residue V (y - y') = 0` using `(residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hy)`. Establish `e5 : W.toAffine.Equation x y` using `(map_equation W.toAffine (f := V.subtype) Subtype.val_injective x y).1 h.1`.

Establish `e6` using `(equation_iff_nonsingular_of_Δ_ne_zero (W := (W.map (residue V)).toAffine) (by rw [map_Δ]; exact (residue_ne_zero_iff_isUnit _).2 hΔ)).1 (e5.map (residue V))`. Establish `f1` using `congrArg (residue V) e1`. Establish `f2` using `congrArg (residue V) e2`. Rewrite `f1` using `[map_mul, e3]`. Rewrite `f2` using `[map_mul, e4]`.

Simplify using `only [map_mul, map_add, map_sub, map_pow] at f1 f2 e3 e4`. Rewrite `e3`, `e4` using `[sub_eq_zero]`. Rewrite `f1`, `f2` using `[← e3]`. Rewrite `f1` using `[← e4]`. Apply the tactic sequence `rcases ((nonsingular_iff' _ _).1 e6).2 with e | e <;> apply e <;>`.

Simplify using `only [map_a₁, map_a₂, map_a₃, map_a₄]`. Take the linear combination `f2`. Take the linear combination `-f1`.
-/
theorem torsion_inj (h20 : (2 : k) ≠ 0) (h2 : (2 : k)⁻¹ ∈ V) (h30 : (3 : k) ≠ 0) (h3 : (3 : k)⁻¹ ∈ V)
    (hΔ : IsUnit W.Δ) {x y x' y' : k} (h : (W.map V.subtype).toAffine.Nonsingular x y)
    (h' : (W.map V.subtype).toAffine.Nonsingular x' y') (h12 : 12 • Point.some x y h = 0)
    (h12' : 12 • Point.some x' y' h' = 0) (hx : x - x' ∈ V.nonunits) (hy : y - y' ∈ V.nonunits) :
    x = x' ∧ y = y' := by
  by_contra hne
  obtain ⟨mx, my⟩ := torsion_mem W h20 h2 h30 h3 h h12
  obtain ⟨mx', my'⟩ := torsion_mem W h20 h2 h30 h3 h' h12'
  have hxy : ¬(x = x' ∧ y = (W.map V.subtype).toAffine.negY x' ((W.map V.subtype).toAffine.negY x' y')) := by
    rwa [negY_negY]
  have hd : 12 • (Point.some x y h + -Point.some x' y' h') = 0 := by
    rw [smul_add, smul_neg, h12, h12', neg_zero, add_zero]
  rw [Point.neg_some, Point.add_some hxy] at hd
  have m3 := (torsion_mem W h20 h2 h30 h3 _ hd).1
  have he := (equation_iff _ _).1 h.1
  have he' := (equation_iff _ _).1 h'.1
  have hl : (W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') * (x - x') =
        y + y' + W.a₁ * x' + W.a₃ ∧
      (W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') * (y - y') =
        x ^ 2 + x * x' + x' ^ 2 + W.a₂ * (x + x') + W.a₄ - W.a₁ * y := by
    by_cases hxx : x = x'
    · have h1 := fun e => hxy ⟨hxx, e⟩
      have h4 := Y_eq_of_Y_ne h.1 ((equation_neg _ _).2 h'.1) hxx h1
      have h5 := slope_of_Y_ne hxx h1
      have h6 : (W.map V.subtype).toAffine.negY x y = y' := by rw [hxx, h4, negY_negY]
      rw [h6, eq_div_iff (sub_ne_zero.2 fun e => hne ⟨hxx, e⟩)] at h5
      rw [h5]
      subst hxx
      simp only [negY, map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.coe_subtype] at h4 ⊢
      exact ⟨by linear_combination -h4, by ring⟩
    · have h0 := sub_ne_zero.2 hxx
      rw [slope_of_X_ne hxx]
      simp only [negY, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.coe_subtype] at he he' ⊢
      constructor
      · field_simp
        ring
      · field_simp
        linear_combination he - he'
  generalize (W.map V.subtype).toAffine.slope x x' y ((W.map V.subtype).toAffine.negY x' y') = l at hl m3
  simp only [addX, map_a₁, map_a₂, ValuationSubring.coe_subtype] at m3
  have ml : l ∈ V := by
    refine mem_of_quartic V (c := 1) one_ne_zero (by simp) W.a₁.2
      (neg_mem (add_mem (add_mem (add_mem m3 W.a₂.2) mx) mx')) V.zero_mem V.zero_mem ?_
    ring
  lift x to V using mx
  lift y to V using my
  lift x' to V using mx'
  lift y' to V using my'
  lift l to V using ml
  have e1 : l * (x - x') = y + y' + W.a₁ * x' + W.a₃ := by exact_mod_cast hl.1
  have e2 : l * (y - y') = x ^ 2 + x * x' + x' ^ 2 + W.a₂ * (x + x') + W.a₄ - W.a₁ * y := by exact_mod_cast hl.2
  have e3 : residue V (x - x') = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hx)
  have e4 : residue V (y - y') = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hy)
  have e5 : W.toAffine.Equation x y := (map_equation W.toAffine (f := V.subtype) Subtype.val_injective x y).1 h.1
  have e6 := (equation_iff_nonsingular_of_Δ_ne_zero (W := (W.map (residue V)).toAffine)
    (by rw [map_Δ]; exact (residue_ne_zero_iff_isUnit _).2 hΔ)).1 (e5.map (residue V))
  have f1 := congrArg (residue V) e1
  have f2 := congrArg (residue V) e2
  rw [map_mul, e3] at f1
  rw [map_mul, e4] at f2
  simp only [map_mul, map_add, map_sub, map_pow] at f1 f2 e3 e4
  rw [sub_eq_zero] at e3 e4
  rw [← e3] at f1 f2
  rw [← e4] at f1
  rcases ((nonsingular_iff' _ _).1 e6).2 with e | e <;> apply e <;>
    simp only [map_a₁, map_a₂, map_a₃, map_a₄]
  · linear_combination f2
  · linear_combination -f1

end Local

section Global

variable {F H M : Type} [Field F] [NumberField F] [Field H] [NumberField H] [Field M] [NumberField M]

/- English proof (translation)
Rewrite `h1` using `[← absNorm_differentIdeal M (𝓞 M)]`. Take `⟨P, hP, hu, hd⟩` from `Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1`. Establish `hpP : (p : 𝓞 M) ∈ P`. Establish `: (p : ℤ) ∈ P.under ℤ` using `hu ▸ Ideal.mem_span_singleton_self _`. Simplify using `using Ideal.mem_comap.1 this`.

Establish `h0 : P ≠ ⊥` using `fun e => hp.ne_zero (by simpa [e] using hpP)`. Use `⟨⟨P, hP.isPrime, h0⟩, hpP, ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H) (𝓞 M)]`. Use `((Ideal.prime_of_isPrime h0 hP.isPrime).dvd_or_dvd hd).resolve_right fun h => ?_` and prove the remaining obligations. Establish `h3` using `Ideal.dvd_iff_le.1 h (Ideal.mem_map_of_mem _ (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 H))))`.

Rewrite `h3` using `[absNorm_differentIdeal H (𝓞 H), map_natCast]`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h2)`. Establish `h4` using `congrArg (Int.cast : ℤ → 𝓞 M) hab`. Rewrite `h4` using `[Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_one]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 (h4 ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ h3)))`.
-/
theorem exists_dvd_different [Algebra H M] {p : ℕ} (hp : p.Prime) (h1 : p ∣ (discr M).natAbs)
    (h2 : ¬ p ∣ (discr H).natAbs) :
    ∃ w : HeightOneSpectrum (𝓞 M), (p : 𝓞 M) ∈ w.asIdeal ∧ w.asIdeal ∣ differentIdeal (𝓞 H) (𝓞 M) := by
  rw [← absNorm_differentIdeal M (𝓞 M)] at h1
  obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
  have hpP : (p : 𝓞 M) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := hu ▸ Ideal.mem_span_singleton_self _
    simpa using Ideal.mem_comap.1 this
  have h0 : P ≠ ⊥ := fun e => hp.ne_zero (by simpa [e] using hpP)
  refine ⟨⟨P, hP.isPrime, h0⟩, hpP, ?_⟩
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H) (𝓞 M)] at hd
  refine ((Ideal.prime_of_isPrime h0 hP.isPrime).dvd_or_dvd hd).resolve_right fun h => ?_
  have h3 := Ideal.dvd_iff_le.1 h (Ideal.mem_map_of_mem _ (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 H))))
  rw [absNorm_differentIdeal H (𝓞 H), map_natCast] at h3
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h2)
  have h4 := congrArg (Int.cast : ℤ → 𝓞 M) hab
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_one] at h4
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h4 ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ h3)))

/- English proof (translation)
The claim follows from `le_antisymm (w.valuation_le_one a) (not_lt.1 fun h => ha ((w.valuation_lt_one_iff_mem a).1 h))`.
-/
theorem valuation_eq_one (w : HeightOneSpectrum (𝓞 M)) {a : 𝓞 M} (ha : a ∉ w.asIdeal) :
    w.valuation M (a : M) = 1 :=
  le_antisymm (w.valuation_le_one a) (not_lt.1 fun h => ha ((w.valuation_lt_one_iff_mem a).1 h))

omit [NumberField H] in

/- English proof (translation)
Take `⟨n, d, h⟩` from `w.exists_primeCompl_mul_eq_of_integer x hx`. Establish `hd : (d : 𝓞 M) ∉ w.asIdeal` using `d.2`. Establish `hd' : σ • (d : 𝓞 M) ∉ w.asIdeal` using `fun e => hd (by simpa using sub_mem e (hσ d))`. Establish `h' : σ x * ((σ • (d : 𝓞 M) : 𝓞 M) : M) = ((σ • n : 𝓞 M) : M)`. Use `congrArg σ h` as an intermediate fact.

Rewrite `this` using `[map_mul]`. Conclude with `this`. Establish `hm : (σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) ∈ w.asIdeal` using `sub_mem (Ideal.mul_mem_right _ _ (hσ n)) (Ideal.mul_mem_left _ _ (hσ d))`. Establish `e : (σ x - x) * ((d : 𝓞 M) : M) * ((σ • (d : 𝓞 M) : 𝓞 M) : M) = (((σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) : 𝓞 M) : M)`. Express the relevant statement in the definitionally equal form `x * ((d : 𝓞 M) : M) = (n : M) at h`.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul] at h h' ⊢`. Take the linear combination `algebraMap (𝓞 M) M d * h' - algebraMap (𝓞 M) M (σ • (d : 𝓞 M)) * h`. Use `(w.valuation_lt_one_iff_mem (K := M) _).2 hm` as an intermediate fact. Express the relevant statement in the definitionally equal form `w.valuation M (((σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) : 𝓞 M) : M) < 1 at this`. Rewrite `this` using `[← e, map_mul, map_mul, valuation_eq_one w hd, valuation_eq_one w hd', mul_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem valuation_sub_lt [Algebra H M] (w : HeightOneSpectrum (𝓞 M)) (σ : M ≃ₐ[H] M)
    (hσ : ∀ x : 𝓞 M, σ • x - x ∈ w.asIdeal) {x : M} (hx : w.valuation M x ≤ 1) : w.valuation M (σ x - x) < 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 M) ∉ w.asIdeal := d.2
  have hd' : σ • (d : 𝓞 M) ∉ w.asIdeal := fun e => hd (by simpa using sub_mem e (hσ d))
  have h' : σ x * ((σ • (d : 𝓞 M) : 𝓞 M) : M) = ((σ • n : 𝓞 M) : M) := by
    have := congrArg σ h
    rw [map_mul] at this
    exact this
  have hm : (σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) ∈ w.asIdeal :=
    sub_mem (Ideal.mul_mem_right _ _ (hσ n)) (Ideal.mul_mem_left _ _ (hσ d))
  have e : (σ x - x) * ((d : 𝓞 M) : M) * ((σ • (d : 𝓞 M) : 𝓞 M) : M) =
      (((σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) : 𝓞 M) : M) := by
    change x * ((d : 𝓞 M) : M) = (n : M) at h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub, map_mul] at h h' ⊢
    linear_combination algebraMap (𝓞 M) M d * h' - algebraMap (𝓞 M) M (σ • (d : 𝓞 M)) * h
  have := (w.valuation_lt_one_iff_mem (K := M) _).2 hm
  change w.valuation M (((σ • n - n) * d - n * (σ • (d : 𝓞 M) - d) : 𝓞 M) : M) < 1 at this
  rwa [← e, map_mul, map_mul, valuation_eq_one w hd, valuation_eq_one w hd', mul_one, mul_one] at this

/- English proof (translation)
Use `valuation_eq_one w hn` as an intermediate fact. Rewrite `this` using `[RingOfIntegers.coe_eq_algebraMap, map_natCast]`. Rewrite using `[Valuation.mem_valuationSubring_iff, map_inv₀, this, inv_one]`.
-/
theorem inv_natCast_mem (w : HeightOneSpectrum (𝓞 M)) {n : ℕ} (hn : (n : 𝓞 M) ∉ w.asIdeal) :
    (n : M)⁻¹ ∈ (w.valuation M).valuationSubring := by
  have := valuation_eq_one w hn
  rw [RingOfIntegers.coe_eq_algebraMap, map_natCast] at this
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, this, inv_one]

open Classical in

/- English proof (translation)
Use `set V := (w.valuation M).valuationSubring with hV`. Use `set R := v.valuationSubringAtPrime F with hR`. Establish `hRV : ∀ r : R, algebraMap F M r ∈ V`. Introduce `r`. Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj v.asIdeal.primeCompl r`.

Establish `hs : algebraMap (𝓞 F) (𝓞 M) s ∉ w.asIdeal` using `fun e => s.2 (hv.ge (Ideal.mem_comap.2 e))`. Establish `e1 : algebraMap F M r * ((algebraMap (𝓞 F) (𝓞 M) s : 𝓞 M) : M) = ((algebraMap (𝓞 F) (𝓞 M) a : 𝓞 M) : M)`. Use `congrArg (fun t : R => algebraMap F M t) e` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, map_mul] at this`. Conclude with `this`.

Establish `e2` using `congrArg (w.valuation M) e1`. Rewrite `e2` using `[map_mul, valuation_eq_one w hs, mul_one]`. Rewrite using `[hV, Valuation.mem_valuationSubring_iff, e2]`. Conclude with `w.valuation_le_one _`. Set `φ : R →+* V` to `((algebraMap F M).comp (algebraMap R F)).codRestrict V hRV`.

Use `hC.toIsMinimal` as an intermediate fact. Set `W` to `((C • A).integralModel R).map φ`. Establish `hW : (C • A).baseChange M = W.map V.subtype` using `by conv_lhs => rw [← baseChange_integralModel_eq R (C • A)]`. Simplify using `only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]`. Both sides reduce to the same expression.

Establish `hΔ : IsUnit W.Δ`. Establish `h1` using `((hasGoodReduction_iff_isElliptic_reduction R).1 hC).isUnit.ne_zero`. Rewrite `h1` using `[reduction, map_Δ]`. Rewrite using `[map_Δ]`. Conclude with `((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).map φ`.

Establish `hCC : C.map (algebraMap F M) • A.baseChange M = (C • A).baseChange M` using `map_variableChange A C _`. Take `⟨_ | ⟨x', y', h'⟩, e⟩` from `(variableChangePoint_bijective _ hCC).2 (Point.some x y h)`. Conclude with `absurd e.symm (Point.some_ne_zero _)`. Establish `t1 : 12 • Point.some x' y' h' = 0` using `(variableChangePoint_bijective _ hCC).1 (by rw [map_nsmul, e, h12, _root_.map_zero])`. Establish `t2` using `congrArg (Point.map (W' := (C • A).toAffine) (σ.restrictScalars F : M →ₐ[F] M)) t1`.

Rewrite `t2` using `[map_nsmul, Point.map_some, _root_.map_zero]`. Establish `key : σ x' = x' ∧ σ y' = y'`. Establish `m2` using `inv_natCast_mem w h2`. Establish `m3` using `inv_natCast_mem w h3`. Rewrite `m2`, `m3` using `[Nat.cast_ofNat]`.

Establish `hn : ∀ z ∈ V, σ z - z ∈ V.nonunits` using `fun z hz => by`. Establish `h1` using `valuation_sub_lt w σ hσ hz`. Rewrite using `[ValuationSubring.mem_nonunits_iff_or, or_iff_not_imp_left]`. Introduce `h0 h4`. Rewrite `h4` using `[hV, Valuation.mem_valuationSubring_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]`.

Conclude with `absurd h1 (not_lt.2 h4)`. Establish `aux : ∀ B : WeierstrassCurve M, B = W.map V.subtype → ∀ (h₁ : B.toAffine.Nonsingular x' y') (h₂ : B.toAffine.Nonsingular (σ x') (σ y')), 12 • Point.some _ _ h₁ = 0 → 12 • Point.some _ _ h₂ = 0 → σ x' = x' ∧ σ y' = y'`. Introduce and unpack `B rfl h₁ h₂ s₁ s₂`. Take `⟨mx, my⟩` from `torsion_mem W two_ne_zero m2 three_ne_zero m3 h₁ s₁`. Conclude with `torsion_inj W two_ne_zero m2 three_ne_zero m3 hΔ h₂ h₁ s₂ s₁ (hn _ mx) (hn _ my)`.

Conclude with `aux _ hW h' _ t1 t2`. Rewrite `e` using `[variableChangePoint_some, Point.some.injEq]`. Establish `hF : ∀ a : F, σ (algebraMap F M a) = algebraMap F M a` using `(σ.restrictScalars F).commutes`. Rewrite using `[← e.1, ← e.2]`. Simplify using `[VariableChange.map, hF, key.1, key.2]`.
-/
theorem inertia_fixes [Algebra F H] [Algebra H M] [Algebra F M] [IsScalarTower F H M] (A : WeierstrassCurve F)
    (w : HeightOneSpectrum (𝓞 M)) (v : HeightOneSpectrum (𝓞 F)) (hv : v.asIdeal = w.asIdeal.under (𝓞 F))
    (h2 : ((2 : ℕ) : 𝓞 M) ∉ w.asIdeal) (h3 : ((3 : ℕ) : 𝓞 M) ∉ w.asIdeal) (C : VariableChange F)
    (hC : (C • A).HasGoodReduction (v.valuationSubringAtPrime F)) (σ : M ≃ₐ[H] M)
    (hσ : ∀ x : 𝓞 M, σ • x - x ∈ w.asIdeal) {x y : M} (h : (A.baseChange M).toAffine.Nonsingular x y)
    (h12 : 12 • Point.some x y h = 0) : σ x = x ∧ σ y = y := by
  set V := (w.valuation M).valuationSubring with hV
  set R := v.valuationSubringAtPrime F with hR
  have hRV : ∀ r : R, algebraMap F M r ∈ V := by
    intro r
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj v.asIdeal.primeCompl r
    have hs : algebraMap (𝓞 F) (𝓞 M) s ∉ w.asIdeal := fun e => s.2 (hv.ge (Ideal.mem_comap.2 e))
    have e1 : algebraMap F M r * ((algebraMap (𝓞 F) (𝓞 M) s : 𝓞 M) : M) = ((algebraMap (𝓞 F) (𝓞 M) a : 𝓞 M) : M) := by
      have := congrArg (fun t : R => algebraMap F M t) e
      simp only [MulMemClass.coe_mul, map_mul] at this
      exact this
    have e2 := congrArg (w.valuation M) e1
    rw [map_mul, valuation_eq_one w hs, mul_one] at e2
    rw [hV, Valuation.mem_valuationSubring_iff, e2]
    exact w.valuation_le_one _
  let φ : R →+* V := ((algebraMap F M).comp (algebraMap R F)).codRestrict V hRV
  have := hC.toIsMinimal
  let W := ((C • A).integralModel R).map φ
  have hW : (C • A).baseChange M = W.map V.subtype := by
    conv_lhs => rw [← baseChange_integralModel_eq R (C • A)]
    simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have hΔ : IsUnit W.Δ := by
    have h1 := ((hasGoodReduction_iff_isElliptic_reduction R).1 hC).isUnit.ne_zero
    rw [reduction, map_Δ] at h1
    rw [map_Δ]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).map φ
  have hCC : C.map (algebraMap F M) • A.baseChange M = (C • A).baseChange M := map_variableChange A C _
  obtain ⟨_ | ⟨x', y', h'⟩, e⟩ := (variableChangePoint_bijective _ hCC).2 (Point.some x y h)
  · exact absurd e.symm (Point.some_ne_zero _)
  have t1 : 12 • Point.some x' y' h' = 0 :=
    (variableChangePoint_bijective _ hCC).1 (by rw [map_nsmul, e, h12, _root_.map_zero])
  have t2 := congrArg (Point.map (W' := (C • A).toAffine) (σ.restrictScalars F : M →ₐ[F] M)) t1
  rw [map_nsmul, Point.map_some, _root_.map_zero] at t2
  have key : σ x' = x' ∧ σ y' = y' := by
    have m2 := inv_natCast_mem w h2
    have m3 := inv_natCast_mem w h3
    rw [Nat.cast_ofNat] at m2 m3
    have hn : ∀ z ∈ V, σ z - z ∈ V.nonunits := fun z hz => by
      have h1 := valuation_sub_lt w σ hσ hz
      rw [ValuationSubring.mem_nonunits_iff_or, or_iff_not_imp_left]
      intro h0 h4
      rw [hV, Valuation.mem_valuationSubring_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))] at h4
      exact absurd h1 (not_lt.2 h4)
    have aux : ∀ B : WeierstrassCurve M, B = W.map V.subtype → ∀ (h₁ : B.toAffine.Nonsingular x' y')
        (h₂ : B.toAffine.Nonsingular (σ x') (σ y')), 12 • Point.some _ _ h₁ = 0 → 12 • Point.some _ _ h₂ = 0 →
        σ x' = x' ∧ σ y' = y' := by
      rintro B rfl h₁ h₂ s₁ s₂
      obtain ⟨mx, my⟩ := torsion_mem W two_ne_zero m2 three_ne_zero m3 h₁ s₁
      exact torsion_inj W two_ne_zero m2 three_ne_zero m3 hΔ h₂ h₁ s₂ s₁ (hn _ mx) (hn _ my)
    exact aux _ hW h' _ t1 t2
  rw [variableChangePoint_some, Point.some.injEq] at e
  have hF : ∀ a : F, σ (algebraMap F M a) = algebraMap F M a := (σ.restrictScalars F).commutes
  rw [← e.1, ← e.2]
  simp [VariableChange.map, hF, key.1, key.2]

end Global

section Field

variable {F H M : Type} [Field F] [NumberField F] [Field H] [NumberField H] [Field M] [NumberField M]
  [Algebra F H] [Algebra H M] [Algebra F M] [IsScalarTower F H M] [Algebra F ℂ] [Algebra H ℂ] [Algebra M ℂ]
  [IsScalarTower F M ℂ] [IsScalarTower H M ℂ] [IsScalarTower F H ℂ] (A : WeierstrassCurve F)
  (hsub : ∀ z ∈ torsionCoords (A.baseChange ℂ) 12, ∃ x : M, algebraMap M ℂ x = z)
  (hgen : ∀ T : Subfield M, (∀ a : H, algebraMap H M a ∈ T) →
    (∀ z : M, algebraMap M ℂ z ∈ torsionCoords (A.baseChange ℂ) 12 → z ∈ T) → ∀ z, z ∈ T)

include hsub

open Classical in

/- English proof (translation)
Take `⟨x, y, h, h12, hz⟩` from `hz`. Take `⟨x, rfl⟩` from `hsub x ⟨x, y, h, h12, Or.inl rfl⟩`. Take `⟨y, rfl⟩` from `hsub y ⟨_, y, h, h12, Or.inr rfl⟩`. Establish `h' : (A.baseChange M).toAffine.Nonsingular x y` using `(baseChange_nonsingular A.toAffine (f := IsScalarTower.toAlgHom F M ℂ) (algebraMap M ℂ).injective x y).1 h`. Use `⟨x, y, h', ?_, hz.imp (fun e => (algebraMap M ℂ).injective e) (fun e => (algebraMap M ℂ).injective e)⟩` and prove the remaining obligations.

Apply `Point.map_injective (W' := A.toAffine) (IsScalarTower.toAlgHom F M ℂ)` to reduce the goal to its premises. Rewrite using `[map_nsmul, Point.map_some, _root_.map_zero]`. Conclude with `h12`.
-/
theorem exists_point {z : M} (hz : algebraMap M ℂ z ∈ torsionCoords (A.baseChange ℂ) 12) :
    ∃ (x y : M) (h : (A.baseChange M).toAffine.Nonsingular x y), 12 • Point.some x y h = 0 ∧ (z = x ∨ z = y) := by
  obtain ⟨x, y, h, h12, hz⟩ := hz
  obtain ⟨x, rfl⟩ := hsub x ⟨x, y, h, h12, Or.inl rfl⟩
  obtain ⟨y, rfl⟩ := hsub y ⟨_, y, h, h12, Or.inr rfl⟩
  have h' : (A.baseChange M).toAffine.Nonsingular x y :=
    (baseChange_nonsingular A.toAffine (f := IsScalarTower.toAlgHom F M ℂ) (algebraMap M ℂ).injective x y).1 h
  refine ⟨x, y, h', ?_, hz.imp (fun e => (algebraMap M ℂ).injective e) (fun e => (algebraMap M ℂ).injective e)⟩
  apply Point.map_injective (W' := A.toAffine) (IsScalarTower.toAlgHom F M ℂ)
  rw [map_nsmul, Point.map_some, _root_.map_zero]
  exact h12

include hgen

/- English proof (translation)
Establish `hφ : ∀ (φ : M →ₐ[H] ℂ) (z : M), φ z ∈ (IsScalarTower.toAlgHom H M ℂ).fieldRange`. Introduce `φ`. Use `hgen ((algebraMap M ℂ).fieldRange.comap φ.toRingHom) (fun a => ⟨algebraMap H M a, ?_⟩) fun z hz => ?_` and prove the remaining obligations. Conclude with `(IsScalarTower.algebraMap_apply H M ℂ a).symm.trans (φ.commutes a).symm`. Take `⟨x, y, h, h12, hz⟩` from `exists_point A hsub hz`.

Establish `t` using `congrArg (Point.map (W' := A.toAffine) (φ.restrictScalars F)) h12`. Rewrite `t` using `[map_nsmul, Point.map_some, _root_.map_zero]`. Use `hsub (φ z) ⟨φ x, φ y, _, t, hz.imp (fun e => by rw [e]) (fun e => by rw [e])⟩` and prove the remaining obligations. Establish `: Normal H M`. Use `normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩` and prove the remaining obligations.

Use `Polynomial.Splits.of_splits_map (algebraMap M ℂ) (IsAlgClosed.splits _) fun a ha => ?_` and prove the remaining obligations. Establish `: a ∈ (minpoly H x).rootSet ℂ`. Rewrite `ha` using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`. Conclude with `Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)`. Rewrite `this` using `[← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]`.

Take `⟨φ, rfl⟩` from `this`. Conclude with `hφ φ x`. Conclude with `IsGalois.mk`.
-/
theorem isGalois : IsGalois H M := by
  classical
  have hφ : ∀ (φ : M →ₐ[H] ℂ) (z : M), φ z ∈ (IsScalarTower.toAlgHom H M ℂ).fieldRange := by
    intro φ
    refine hgen ((algebraMap M ℂ).fieldRange.comap φ.toRingHom) (fun a => ⟨algebraMap H M a, ?_⟩) fun z hz => ?_
    · exact (IsScalarTower.algebraMap_apply H M ℂ a).symm.trans (φ.commutes a).symm
    · obtain ⟨x, y, h, h12, hz⟩ := exists_point A hsub hz
      have t := congrArg (Point.map (W' := A.toAffine) (φ.restrictScalars F)) h12
      rw [map_nsmul, Point.map_some, _root_.map_zero] at t
      refine hsub (φ z) ⟨φ x, φ y, _, t, hz.imp (fun e => by rw [e]) (fun e => by rw [e])⟩
  have : Normal H M := by
    refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    refine Polynomial.Splits.of_splits_map (algebraMap M ℂ) (IsAlgClosed.splits _) fun a ha => ?_
    have : a ∈ (minpoly H x).rootSet ℂ := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at this
    obtain ⟨φ, rfl⟩ := this
    exact hφ φ x
  exact IsGalois.mk

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or]`. Use `isGalois A hsub hgen` as an intermediate fact. Take `⟨w, hpw, hw⟩` from `exists_dvd_different hp h hc.2`. Establish `hn : ∀ n : ℕ, n ∣ 6 * d → (n : 𝓞 M) ∉ w.asIdeal`.

Introduce `n hn hnw`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun e => hc.1 (e.trans hn))`. Establish `h4` using `congrArg (Int.cast : ℤ → 𝓞 M) hab`. Rewrite `h4` using `[Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_one]`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h4 ▸ add_mem (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hnw)))`.

Use `w.isPrime` as an intermediate fact. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨w.asIdeal.under (𝓞 F), inferInstance, mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot⟩`. Take `⟨C, hC⟩` from `hA v fun e => hn d (Dvd.intro_left _ rfl) (by simpa using Ideal.mem_comap.1 e)`. Use `GlobalTheory.DifferentBound.not_dvd_of_inertia H M w.asIdeal w.ne_bot (fun σ hσ => ?_) hw` and prove the remaining obligations. Use extensionality with `z`.

Use `hgen (RingHom.eqLocusField (σ : M →+* M) (RingHom.id M)) σ.commutes (fun z hz => ?_) z` and prove the remaining obligations. Take `⟨x, y, h, h12, hz⟩` from `exists_point A hsub hz`. Use `inertia_fixes A w v rfl (hn 2 ⟨3 * d, by ring⟩) (hn 3 ⟨2 * d, by ring⟩) C hC σ hσ h h12` as an intermediate fact. Break down `hz with rfl | rfl` into its components or cases. Conclude with `this.1`.

Conclude with `this.2`.
-/
theorem dvd_or_dvd (d : ℕ) (hA : HasGoodReductionOutside d A) (p : ℕ) (hp : p.Prime)
    (h : p ∣ (discr M).natAbs) : p ∣ 6 * d ∨ p ∣ (discr H).natAbs := by
  by_contra hc
  rw [not_or] at hc
  have := isGalois A hsub hgen
  obtain ⟨w, hpw, hw⟩ := exists_dvd_different hp h hc.2
  have hn : ∀ n : ℕ, n ∣ 6 * d → (n : 𝓞 M) ∉ w.asIdeal := by
    intro n hn hnw
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2
      ((Nat.Prime.coprime_iff_not_dvd hp).2 fun e => hc.1 (e.trans hn))
    have h4 := congrArg (Int.cast : ℤ → 𝓞 M) hab
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_one] at h4
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (h4 ▸ add_mem (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hnw)))
  have := w.isPrime
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨w.asIdeal.under (𝓞 F), inferInstance, mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot⟩
  obtain ⟨C, hC⟩ := hA v fun e => hn d (Dvd.intro_left _ rfl) (by simpa using Ideal.mem_comap.1 e)
  refine GlobalTheory.DifferentBound.not_dvd_of_inertia H M w.asIdeal w.ne_bot (fun σ hσ => ?_) hw
  ext z
  refine hgen (RingHom.eqLocusField (σ : M →+* M) (RingHom.id M)) σ.commutes (fun z hz => ?_) z
  obtain ⟨x, y, h, h12, hz⟩ := exists_point A hsub hz
  have := inertia_fixes A w v rfl (hn 2 ⟨3 * d, by ring⟩) (hn 3 ⟨2 * d, by ring⟩) C hC σ hσ h h12
  rcases hz with rfl | rfl
  · exact this.1
  · exact this.2

end Field

/- English proof (translation)
Establish `h2 : H ≤ M` using `le_sup_left.trans hM.ge`. Establish `h3 : IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12) ≤ M` using `le_sup_right.trans hM.ge`. Set `: Algebra F H` to `(IntermediateField.inclusion h1).toRingHom.toAlgebra`. Set `: Algebra H M` to `(IntermediateField.inclusion h2).toRingHom.toAlgebra`. Set `: Algebra F M` to `(IntermediateField.inclusion (h1.trans h2)).toRingHom.toAlgebra`.

Establish `: IsScalarTower F H M` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower F H ℂ` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower F M ℂ` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower H M ℂ` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `dvd_or_dvd A (fun z hz => ⟨⟨z, h3 (IntermediateField.subset_adjoin ℚ _ hz)⟩, rfl⟩) ?_ d hA p hp h` and prove the remaining obligations.

Introduce `T hH hS z`. Set `T' : IntermediateField ℚ ℂ` to `(T.map (algebraMap M ℂ)).toIntermediateField fun q => by`. Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem _ q`. Establish `h4 : M ≤ T'`.

Use `hM.le.trans (sup_le (fun a ha => ⟨_, hH ⟨a, ha⟩, rfl⟩) (IntermediateField.adjoin_le_iff.2 fun a ha => ?_))` and prove the remaining obligations. Conclude with `⟨⟨a, h3 (IntermediateField.subset_adjoin ℚ _ ha)⟩, hS _ ha, rfl⟩`. Take `⟨t, ht, e⟩` from `h4 z.2`. Rewrite using `[← show t = z from Subtype.ext e]` and apply the resulting hypothesis.
-/
theorem dvd_or_dvd_of_eq (d : ℕ) (F H M : IntermediateField ℚ ℂ) [NumberField F] [NumberField H] [NumberField M]
    (A : WeierstrassCurve F) (h1 : F ≤ H)
    (hM : M = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12)) (hA : HasGoodReductionOutside d A)
    (p : ℕ) (hp : p.Prime) (h : p ∣ (discr M).natAbs) : p ∣ 6 * d ∨ p ∣ (discr H).natAbs := by
  have h2 : H ≤ M := le_sup_left.trans hM.ge
  have h3 : IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12) ≤ M := le_sup_right.trans hM.ge
  let : Algebra F H := (IntermediateField.inclusion h1).toRingHom.toAlgebra
  let : Algebra H M := (IntermediateField.inclusion h2).toRingHom.toAlgebra
  let : Algebra F M := (IntermediateField.inclusion (h1.trans h2)).toRingHom.toAlgebra
  have : IsScalarTower F H M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F H ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower H M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine dvd_or_dvd A (fun z hz => ⟨⟨z, h3 (IntermediateField.subset_adjoin ℚ _ hz)⟩, rfl⟩) ?_ d hA p hp h
  intro T hH hS z
  let T' : IntermediateField ℚ ℂ := (T.map (algebraMap M ℂ)).toIntermediateField fun q => by
    rw [eq_ratCast]
    exact SubfieldClass.ratCast_mem _ q
  have h4 : M ≤ T' := by
    refine hM.le.trans
      (sup_le (fun a ha => ⟨_, hH ⟨a, ha⟩, rfl⟩) (IntermediateField.adjoin_le_iff.2 fun a ha => ?_))
    exact ⟨⟨a, h3 (IntermediateField.subset_adjoin ℚ _ ha)⟩, hS _ ha, rfl⟩
  obtain ⟨t, ht, e⟩ := h4 z.2
  rwa [← show t = z from Subtype.ext e]

/- English proof (translation)
Introduce `d F _ A _ _ _ hA` and use `dvd_or_dvd_of_eq d F _ _ A le_sup_right rfl hA`.
-/
theorem dvd_discr_torsionField : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [NumberField F] (A : WeierstrassCurve F)
    [A.IsElliptic] [NumberField (hilbertField d F)] [NumberField (torsionField d A)], HasGoodReductionOutside d A →
    ∀ p : ℕ, p.Prime → p ∣ (discr (torsionField d A)).natAbs →
      p ∣ 6 * d ∨ p ∣ (discr (hilbertField d F)).natAbs :=
  fun d F _ A _ _ _ hA => dvd_or_dvd_of_eq d F _ _ A le_sup_right rfl hA

end GlobalTheory.Mem.TorsionRam
