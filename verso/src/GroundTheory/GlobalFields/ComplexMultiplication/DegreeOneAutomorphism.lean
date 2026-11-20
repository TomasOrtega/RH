import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunctionAutomorphisms
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
  GroundTheory.Arith.Abelian

universe u

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

/- English proof (translation)
Establish `hmul` using `ψ.ramIdx_mul_card_ker`. Rewrite `hmul` using `[h]`. Establish `hram : ψ.ramIdx = 1` using `(mul_eq_one.mp hmul).1`. Establish `hbot : ψ.pointHom.ker = ⊥` using `AddSubgroup.card_eq_one.mp (mul_eq_one.mp hmul).2`. Establish `hne : ∀ R : A.toAffine.Point, R ≠ 0 → ψ.pointMap R ≠ 0`.

Introduce `R hR h0`. Establish `hR' : R ∈ ψ.pointHom.ker`. Rewrite using `[AddMonoidHom.mem_ker, Isogeny.pointHom_apply]`. Conclude with `h0`. Rewrite `hR'` using `[hbot, AddSubgroup.mem_bot]`.

Conclude with `hR hR'`. Establish `hval : ∀ (R : A.toAffine.Point) (f : B.toAffine.FunctionField), valuationPoint A R (ψ.comap f) = valuationPoint B (ψ.pointMap R) f`. Introduce `R f`. Rewrite using `[ψ.valuationPoint_comap, hram, pow_one]`. Establish `h0 : ψ.pointMap 0 = 0` using `map_zero ψ.pointHom`.

Establish `hinf : ∀ f : B.toAffine.FunctionField, valuationInfty A (ψ.comap f) = valuationInfty B f`. Introduce `f`. Rewrite using `[← valuationPoint_zero_eq, hval, h0, valuationPoint_zero_eq]`. Take `⟨α, β, hα, hf⟩` from `exists_eq_linear_of_valuation (W := A) (f := ψ.comap (genX B)) (fun R hR => by rw [hval]; exact valuationPoint_genX_le_one (hne R hR)) (by rw [hinf, valuationInfty_genX B])`. Take `⟨γ, δ, ε, hγ, hg⟩` from `exists_eq_genY_form_of_valuation (W := A) (g := ψ.comap (genY B)) (fun R hR => by rw [hval]; exact valuationPoint_genY_le_one (hne R hR)) (by rw [hinf, valuationInfty_genY B])`.

Use `set ι := algebraMap F A.toAffine.FunctionField with hι`. Establish `hx : ψ.x = ι α * genX A + ι β` using `by rw [← ψ.comap_genX]; exact hf`. Establish `hy : ψ.y = ι γ * genY A + ι δ * genX A + ι ε` using `by rw [← ψ.comap_genY]; exact hg`. Establish `hN` using `ψ.nonsingular`. Establish `eB` using `(equation_iff _ _).mp hN.1`.

Rewrite `eB` using `[hx, hy]`. Simplify using `only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eB`. Establish `eA` using `genY_sq_add A`. Use `set P : F[X] := C (γ ^ 2 - α ^ 3) * X ^ 3 + C (γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2) * X ^ 2 + C (γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 - 2 * B.a₂ * α * β - B.a₄ * α) * X + C (γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε …`. Use `set Q : F[X] := C (2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁) * X + C (2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃) with hQ`.

Establish `key : algebraMap F[X] A.toAffine.FunctionField P + algebraMap F[X] A.toAffine.FunctionField Q * genY A = 0`. Simplify using `only [hP, hQ, map_add, map_mul, map_pow, algebraMap_C_functionField, ← genX_eq, map_sub, map_ofNat]`. Take the linear combination `eB - ι γ ^ 2 * eA`. Take `⟨hP0, hQ0⟩` from `eq_zero_of_algebraMap_add_mul_genY A key`. Establish `c3` using `congrArg (Polynomial.coeff · 3) hP0`.

Establish `c2` using `congrArg (Polynomial.coeff · 2) hP0`. Establish `c1` using `congrArg (Polynomial.coeff · 1) hP0`. Establish `c0` using `congrArg (Polynomial.coeff · 0) hP0`. Establish `d1` using `congrArg (Polynomial.coeff · 1) hQ0`. Establish `d0` using `congrArg (Polynomial.coeff · 0) hQ0`.

Simplify using `only [hP, hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c3 c2 c1 c0 d1 d0`. Evaluate the numerical expressions using `at c3 c2 c1 c0 d1 d0`. Use `⟨α, β, γ, δ, ε, hα, hγ, hx, hy, by linear_combination c3, by linear_combination c2, by linear_combination c1, by linear_combination c0, by linear_combination d1, by linear_combination d0⟩` and prove the remaining obligations.
-/
theorem exists_coeffs_of_degree_eq_one_of_isAlgClosed (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α β γ δ ε : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A +
        algebraMap F A.toAffine.FunctionField β ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A +
        algebraMap F A.toAffine.FunctionField δ * genX A +
        algebraMap F A.toAffine.FunctionField ε ∧
      γ ^ 2 = α ^ 3 ∧
      γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2 = 0 ∧
      γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
        2 * B.a₂ * α * β - B.a₄ * α = 0 ∧
      γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β -
        B.a₆ = 0 ∧
      2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁ = 0 ∧
      2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃ = 0 := by
  have hmul := ψ.ramIdx_mul_card_ker
  rw [h] at hmul
  have hram : ψ.ramIdx = 1 := (mul_eq_one.mp hmul).1
  have hbot : ψ.pointHom.ker = ⊥ := AddSubgroup.card_eq_one.mp (mul_eq_one.mp hmul).2
  have hne : ∀ R : A.toAffine.Point, R ≠ 0 → ψ.pointMap R ≠ 0 := by
    intro R hR h0
    have hR' : R ∈ ψ.pointHom.ker := by
      rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]; exact h0
    rw [hbot, AddSubgroup.mem_bot] at hR'
    exact hR hR'
  have hval : ∀ (R : A.toAffine.Point) (f : B.toAffine.FunctionField),
      valuationPoint A R (ψ.comap f) = valuationPoint B (ψ.pointMap R) f := by
    intro R f
    rw [ψ.valuationPoint_comap, hram, pow_one]
  have h0 : ψ.pointMap 0 = 0 := map_zero ψ.pointHom
  have hinf : ∀ f : B.toAffine.FunctionField, valuationInfty A (ψ.comap f) = valuationInfty B f := by
    intro f
    rw [← valuationPoint_zero_eq, hval, h0, valuationPoint_zero_eq]
  obtain ⟨α, β, hα, hf⟩ := exists_eq_linear_of_valuation (W := A) (f := ψ.comap (genX B))
    (fun R hR => by rw [hval]; exact valuationPoint_genX_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genX B])
  obtain ⟨γ, δ, ε, hγ, hg⟩ := exists_eq_genY_form_of_valuation (W := A) (g := ψ.comap (genY B))
    (fun R hR => by rw [hval]; exact valuationPoint_genY_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genY B])
  set ι := algebraMap F A.toAffine.FunctionField with hι
  have hx : ψ.x = ι α * genX A + ι β := by rw [← ψ.comap_genX]; exact hf
  have hy : ψ.y = ι γ * genY A + ι δ * genX A + ι ε := by rw [← ψ.comap_genY]; exact hg
  have hN := ψ.nonsingular
  have eB := (equation_iff _ _).mp hN.1
  rw [hx, hy] at eB
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eB
  have eA := genY_sq_add A
  set P : F[X] := C (γ ^ 2 - α ^ 3) * X ^ 3 +
    C (γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2) * X ^ 2 +
    C (γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
      2 * B.a₂ * α * β - B.a₄ * α) * X +
    C (γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β - B.a₆)
    with hP
  set Q : F[X] := C (2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁) * X +
    C (2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃) with hQ
  have key : algebraMap F[X] A.toAffine.FunctionField P +
      algebraMap F[X] A.toAffine.FunctionField Q * genY A = 0 := by
    simp only [hP, hQ, map_add, map_mul, map_pow, algebraMap_C_functionField, ← genX_eq, map_sub,
      map_ofNat]
    linear_combination eB - ι γ ^ 2 * eA
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_algebraMap_add_mul_genY A key
  have c3 := congrArg (Polynomial.coeff · 3) hP0
  have c2 := congrArg (Polynomial.coeff · 2) hP0
  have c1 := congrArg (Polynomial.coeff · 1) hP0
  have c0 := congrArg (Polynomial.coeff · 0) hP0
  have d1 := congrArg (Polynomial.coeff · 1) hQ0
  have d0 := congrArg (Polynomial.coeff · 0) hQ0
  simp only [hP, hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c3 c2 c1 c0 d1 d0
  norm_num at c3 c2 c1 c0 d1 d0
  refine ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, by linear_combination c3, by linear_combination c2,
    by linear_combination c1, by linear_combination c0, by linear_combination d1,
    by linear_combination d0⟩

/- English proof (translation)
Take `⟨α, β, γ, δ, ε, hα, hγ, hx, hy, c3, c2, c1, c0, d1, d0⟩` from `exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h`. Rewrite `*` using `[hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, hB.a₁_eq, hB.a₂_eq, hB.a₃_eq]`. Establish `hδ : δ = 0`. Establish `: (2 * γ) * δ = 0` using `by linear_combination d1`. Conclude with `(mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)`.

Establish `hε : ε = 0`. Establish `: (2 * γ) * ε = 0` using `by linear_combination d0`. Conclude with `(mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)`. Substitute `hδ hε` using the available equality. Establish `hβ : β = 0`.

Establish `: (3 * α ^ 2) * β = 0` using `by linear_combination -c2`. Conclude with `(mul_eq_zero.mp this).resolve_left (mul_ne_zero h3 (pow_ne_zero 2 hα))`. Substitute `hβ` using the available equality. Use `⟨α, γ, hα, hγ, by simpa using hx, by simpa using hy, c3, by linear_combination c1, by linear_combination c0⟩` and prove the remaining obligations.
-/
theorem exists_scale_of_degree_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α γ : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A ∧
      γ ^ 2 = α ^ 3 ∧ γ ^ 2 * A.a₄ = B.a₄ * α ∧ γ ^ 2 * A.a₆ = B.a₆ := by
  obtain ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, c3, c2, c1, c0, d1, d0⟩ :=
    exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h
  rw [hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, hB.a₁_eq, hB.a₂_eq, hB.a₃_eq] at *
  have hδ : δ = 0 := by
    have : (2 * γ) * δ = 0 := by linear_combination d1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  have hε : ε = 0 := by
    have : (2 * γ) * ε = 0 := by linear_combination d0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  subst hδ hε
  have hβ : β = 0 := by
    have : (3 * α ^ 2) * β = 0 := by linear_combination -c2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h3 (pow_ne_zero 2 hα))
  subst hβ
  refine ⟨α, γ, hα, hγ, by simpa using hx, by simpa using hy, c3, by linear_combination c1,
    by linear_combination c0⟩

end AlgClosed

section General

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]

omit [A.IsElliptic] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp [WeierstrassCurve.baseChange, hW.a₁_eq], by simp [WeierstrassCurve.baseChange, hW.a₂_eq], by simp [WeierstrassCurve.baseChange, hW.a₃_eq]⟩`.
-/
theorem IsShortForm.baseChange {W : WeierstrassCurve F} (hW : IsShortForm W) (L : Type*) [Field L]
    [Algebra F L] : IsShortForm (W.baseChange L) :=
  ⟨by simp [WeierstrassCurve.baseChange, hW.a₁_eq], by simp [WeierstrassCurve.baseChange, hW.a₂_eq],
    by simp [WeierstrassCurve.baseChange, hW.a₃_eq]⟩

/- English proof (translation)
Set `Ω` to `AlgebraicClosure F`. Establish `hd : (isogBaseChange (F'` using `Ω) ψ).degree = 1 := by rw [degree_isogBaseChange, h]`. Establish `inj` using `(algebraMap F Ω).injective`. Establish `h2' : (2 : Ω) ≠ 0`. Use `(_root_.map_ne_zero (algebraMap F Ω)).mpr h2` as an intermediate fact.

Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `h3' : (3 : Ω) ≠ 0`. Use `(_root_.map_ne_zero (algebraMap F Ω)).mpr h3` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨α, γ, hα, hγ, hx, hy, hc, h4, h6⟩` from `exists_scale_of_degree_eq_one_of_isAlgClosed h2' h3' (hA.baseChange Ω) (hB.baseChange Ω) _ hd`.

Rewrite `hx` using `[isogBaseChange_alt, ← bcEmb_genX]`. Rewrite `hy` using `[isogBaseChange_y, ← bcEmb_genY]`. Establish `hX0 : genX A ≠ 0` using `fun h => transcendental_genX A (h ▸ isAlgebraic_zero)`. Establish `hY0 : genY A ≠ 0` using `genY_ne_zero A`. Use `set K' := (A.baseChange Ω).toAffine.FunctionField`.

Establish `hXb : bcEmb (F'` using `Ω) A (genX A) ≠ 0 := (_root_.map_ne_zero _).mpr hX0`. Establish `hYb : bcEmb (F'` using `Ω) A (genY A) ≠ 0 := (_root_.map_ne_zero _).mpr hY0`. Establish `ex : bcEmb (F'` using `Ω) A (ψ.x / genX A) = algebraMap Ω K' α := by`. Rewrite using `[map_div₀, hx, mul_div_cancel_right₀ _ hXb]`. Establish `ey : bcEmb (F'` using `Ω) A (ψ.y / genY A) = algebraMap Ω K' γ := by`.

Rewrite using `[map_div₀, hy, mul_div_cancel_right₀ _ hYb]`. Take `⟨a, ha⟩` from `exists_algebraMap_eq_of_bcEmb A ex`. Take `⟨c, hc'⟩` from `exists_algebraMap_eq_of_bcEmb A ey`. Establish `key : ∀ (b : F) (f : A.toAffine.FunctionField) (β : Ω), algebraMap F A.toAffine.FunctionField b = f → bcEmb (F'` using `Ω) A f = algebraMap Ω K' β → algebraMap F Ω b = β := by`. Introduce `b f β hb hf`.

Apply `(algebraMap Ω K').injective` to reduce the goal to its premises. Rewrite using `[← hf, ← hb, AlgHom.commutes, IsScalarTower.algebraMap_apply F Ω K']`. Establish `haα` using `key a _ α ha ex`. Establish `hcγ` using `key c _ γ hc' ey`. Establish `ha0 : a ≠ 0` using `by rintro rfl; exact hα (by rw [← haα, map_zero])`.

Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hγ (by rw [← hcγ, map_zero])`. Establish `hca : c ^ 2 = a ^ 3` using `inj (by rw [map_pow, map_pow, haα, hcγ, hc])`. Establish `h4' : c ^ 2 * A.a₄ = B.a₄ * a` using `inj (by`. Rewrite using `[map_mul, map_mul, map_pow, haα, hcγ]`. Conclude with `h4)`.

Establish `h6' : c ^ 2 * A.a₆ = B.a₆` using `inj (by`. Rewrite using `[map_mul, map_pow, hcγ]`. Conclude with `h6)`. Set `v : Fˣ` to `Units.mk0 (c / a) (div_ne_zero hc0 ha0)`. Establish `hv2 : (v : F) ^ 2 = a` using `by show (c / a) ^ 2 = a`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hca`. Establish `hv3 : (v : F) ^ 3 = c` using `by show (c / a) ^ 3 = c`. Establish `hc2 : c ^ 2 ≠ 0` using `pow_ne_zero 2 hc0`. Rewrite using `[div_pow, ← hca, div_eq_iff hc2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hv0 : (v : F) ^ 2 ≠ 0` using `pow_ne_zero 2 v.ne_zero`. Use `⟨v, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv2, ha, div_mul_cancel₀ _ hX0]`. Rewrite using `[hv3, hc', div_mul_cancel₀ _ hY0]`.

Apply `mul_right_cancel₀ hv0` to reduce the goal to its premises. Rewrite using `[hv2, ← h4', ← hv3, ← hv2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h6', ← hv3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_scale_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hA : IsShortForm A)
    (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A ∧
      B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ := by
  classical
  let Ω := AlgebraicClosure F
  have hd : (isogBaseChange (F' := Ω) ψ).degree = 1 := by rw [degree_isogBaseChange, h]
  have inj := (algebraMap F Ω).injective
  have h2' : (2 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h2
    rwa [map_ofNat] at this
  have h3' : (3 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h3
    rwa [map_ofNat] at this
  obtain ⟨α, γ, hα, hγ, hx, hy, hc, h4, h6⟩ := exists_scale_of_degree_eq_one_of_isAlgClosed h2' h3'
    (hA.baseChange Ω) (hB.baseChange Ω) _ hd
  rw [isogBaseChange_alt, ← bcEmb_genX] at hx
  rw [isogBaseChange_y, ← bcEmb_genY] at hy
  have hX0 : genX A ≠ 0 := fun h => transcendental_genX A (h ▸ isAlgebraic_zero)
  have hY0 : genY A ≠ 0 := genY_ne_zero A
  set K' := (A.baseChange Ω).toAffine.FunctionField
  have hXb : bcEmb (F' := Ω) A (genX A) ≠ 0 := (_root_.map_ne_zero _).mpr hX0
  have hYb : bcEmb (F' := Ω) A (genY A) ≠ 0 := (_root_.map_ne_zero _).mpr hY0
  have ex : bcEmb (F' := Ω) A (ψ.x / genX A) = algebraMap Ω K' α := by
    rw [map_div₀, hx, mul_div_cancel_right₀ _ hXb]
  have ey : bcEmb (F' := Ω) A (ψ.y / genY A) = algebraMap Ω K' γ := by
    rw [map_div₀, hy, mul_div_cancel_right₀ _ hYb]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_bcEmb A ex
  obtain ⟨c, hc'⟩ := exists_algebraMap_eq_of_bcEmb A ey
  have key : ∀ (b : F) (f : A.toAffine.FunctionField) (β : Ω),
      algebraMap F A.toAffine.FunctionField b = f → bcEmb (F' := Ω) A f = algebraMap Ω K' β →
        algebraMap F Ω b = β := by
    intro b f β hb hf
    apply (algebraMap Ω K').injective
    rw [← hf, ← hb, AlgHom.commutes, IsScalarTower.algebraMap_apply F Ω K']
  have haα := key a _ α ha ex
  have hcγ := key c _ γ hc' ey
  have ha0 : a ≠ 0 := by rintro rfl; exact hα (by rw [← haα, map_zero])
  have hc0 : c ≠ 0 := by rintro rfl; exact hγ (by rw [← hcγ, map_zero])
  have hca : c ^ 2 = a ^ 3 := inj (by rw [map_pow, map_pow, haα, hcγ, hc])
  have h4' : c ^ 2 * A.a₄ = B.a₄ * a := inj (by
    rw [map_mul, map_mul, map_pow, haα, hcγ]; exact h4)
  have h6' : c ^ 2 * A.a₆ = B.a₆ := inj (by
    rw [map_mul, map_pow, hcγ]; exact h6)
  let v : Fˣ := Units.mk0 (c / a) (div_ne_zero hc0 ha0)
  have hv2 : (v : F) ^ 2 = a := by
    show (c / a) ^ 2 = a
    field_simp
    linear_combination hca
  have hv3 : (v : F) ^ 3 = c := by
    show (c / a) ^ 3 = c
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
    rw [div_pow, ← hca, div_eq_iff hc2]
    ring
  have hv0 : (v : F) ^ 2 ≠ 0 := pow_ne_zero 2 v.ne_zero
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv2, ha, div_mul_cancel₀ _ hX0]
  · rw [hv3, hc', div_mul_cancel₀ _ hY0]
  · apply mul_right_cancel₀ hv0
    rw [hv2, ← h4', ← hv3, ← hv2]
    ring
  · rw [← h6', ← hv3]
    ring

end General

end GroundTheory.Global
