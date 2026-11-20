import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinB

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def bs (b : Basis ι ℤ Y) (a : ι) : Y →ₗ[ℤ] ℝ := Algebra.linearMap ℤ ℝ ∘ₗ b.coord a

/- English proof (translation)
Simplify using `[bs]`.
-/
theorem bs_apply (b : Basis ι ℤ Y) (a : ι) (y : Y) : bs b a y = (b.repr y a : ℝ) := by
  simp [bs]

/- English proof (translation)
Use `conv_rhs => rw [← b.sum_repr v, ← b.sum_repr w]`. Simplify using `only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, bs_apply, zsmul_eq_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_expand (b : Basis ι ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v w : Y) :
    ∑ a, ∑ c, β (b a) (b c) * (bs b a v * bs b c w) = β v w := by
  conv_rhs => rw [← b.sum_repr v, ← b.sum_repr w]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, bs_apply, zsmul_eq_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

section Repro

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

/- English proof (translation)
Use `set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB`. Take `⟨_, hbal⟩` from `β.2`. Establish `hj : ∀ j, ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i) = star (σ (RingOfIntegers.basis E j : E)) * comp (B.flip z) σ y`. Introduce `j`. Take `⟨c, hc⟩` from `cj_integral hcj (RingOfIntegers.basis E j)`.

Establish `hcc : ((RingOfIntegers.basis E j : 𝓞 E) : E) = cj (c : E)` using `by rw [hc, cj_cj hcj]`. Establish `e : ∀ i, B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) = B (RingOfIntegers.basis E i • (c • y)) z`. Introduce `i`. Rewrite using `[← hbal c _ hcc, smul_comm]`. Repeatedly rewrite using `[e]`.

Rewrite using `[show ∑ i, (B (RingOfIntegers.basis E i • (c • y)) z : ℂ) * σ (ed E i) = comp (B.flip z) σ (c • y) from rfl, comp_smul, hc, hcj]`. Establish `e2 : ∀ c, conj (comp (bs b c) σ z) = ∑ j, (bs b c (RingOfIntegers.basis E j • z) : ℂ) * conj (σ (ed E j))`. Introduce `c`. Simplify using `[comp, map_sum]`. Establish `expand : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z)) = ∑ j, conj (σ (ed E j)) * ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i)`.

Repeatedly rewrite using `[← gram_expand b B (RingOfIntegers.basis E _ • y) (RingOfIntegers.basis E _ • z)]`. Repeatedly rewrite using `[e2]`. Simplify using `only [comp, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum, Complex.ofReal_mul]`. Use `conv_lhs => arg 2`. Use extensionality with `a`.

Rewrite using `[Finset.sum_comm]`. Use `arg 2`. Use extensionality with `i`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`.

Use `conv_lhs => arg 2`. Use extensionality with `i`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[expand]`. Repeatedly rewrite using `[hj]`. Repeatedly rewrite using `[← mul_assoc, ← Finset.sum_mul]`. Establish `ho` using `ortho σ σ`. Simplify using `only [if_true, integralBasis_apply] at ho`.

Establish `: ∑ j, conj (σ (ed E j)) * star (σ (RingOfIntegers.basis E j : E)) = 1`. Use `congrArg conj ho` as an intermediate fact. Simplify `this` using `[map_sum, map_mul]`. Rewrite using `[this, one_mul]`.
-/
theorem repro_sigma (b : Basis ι ℤ Y) (β : SymB cj Y) (σ : E →+* ℂ) (y z : Y) :
    ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      comp ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ).flip z) σ y := by
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  obtain ⟨_, hbal⟩ := β.2

  have hj : ∀ j, ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i)
      = star (σ (RingOfIntegers.basis E j : E)) * comp (B.flip z) σ y := by
    intro j
    obtain ⟨c, hc⟩ := cj_integral hcj (RingOfIntegers.basis E j)
    have hcc : ((RingOfIntegers.basis E j : 𝓞 E) : E) = cj (c : E) := by rw [hc, cj_cj hcj]
    have e : ∀ i, B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) =
        B (RingOfIntegers.basis E i • (c • y)) z := by
      intro i
      rw [← hbal c _ hcc, smul_comm]
    simp_rw [e]
    rw [show ∑ i, (B (RingOfIntegers.basis E i • (c • y)) z : ℂ) * σ (ed E i) = comp (B.flip z) σ (c • y)
      from rfl, comp_smul, hc, hcj]
  have e2 : ∀ c, conj (comp (bs b c) σ z) =
      ∑ j, (bs b c (RingOfIntegers.basis E j • z) : ℂ) * conj (σ (ed E j)) := by
    intro c
    simp [comp, map_sum]
  have expand : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      ∑ j, conj (σ (ed E j)) * ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) *
        σ (ed E i) := by
    simp_rw [← gram_expand b B (RingOfIntegers.basis E _ • y) (RingOfIntegers.basis E _ • z)]
    simp_rw [e2]
    simp only [comp, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum,
      Complex.ofReal_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [expand]
  simp_rw [hj]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have ho := ortho σ σ
  simp only [if_true, integralBasis_apply] at ho
  have : ∑ j, conj (σ (ed E j)) * star (σ (RingOfIntegers.basis E j : E)) = 1 := by
    have := congrArg conj ho
    simpa [map_sum, map_mul] using this
  rw [this, one_mul]

/- English proof (translation)
Take `⟨hs, _⟩` from `β.2`. Use `set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB`. Establish `key : ∀ σ : E →+* ℂ, ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) = 2 * comp (B.flip z) σ y`. Introduce `σ`. Simplify using `only [mul_add, Finset.sum_add_distrib]`.

Establish `sw : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b c) σ y * conj (comp (bs b a) σ z)) = ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z))`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hs (b w) (b x)]`. Rewrite using `[sw, repro_sigma hcj b β σ y z]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `Pf`. Establish `e : ∀ a c, B (b a) (b c) * (∑ σ : E →+* ℂ, (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z))).re = (∑ σ : E →+* ℂ, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) …`. Introduce `a c`. Rewrite using `[← Complex.re_ofReal_mul, Finset.mul_sum]`.

Repeatedly rewrite using `[e]`. Repeatedly rewrite using `[← Complex.re_sum]`. Use `conv_lhs => arg 1`. Use `arg 2`. Use extensionality with `a`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[key]`. Rewrite using `[← Finset.mul_sum, sum_comp]`. Simplify using `[LinearMap.flip_apply]`.
-/
theorem fock_reproducing_formula (b : Basis ι ℤ Y) (β : SymB cj Y) (y z : Y) :
    ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * Pf E (bs b a) (bs b c) y z =
      2 * (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z := by
  obtain ⟨hs, _⟩ := β.2
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  have key : ∀ σ : E →+* ℂ, ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
      2 * comp (B.flip z) σ y := by
    intro σ
    simp only [mul_add, Finset.sum_add_distrib]
    have sw : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
        ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hs (b w) (b x)]
    rw [sw, repro_sigma hcj b β σ y z]
    ring
  unfold Pf
  have e : ∀ a c, B (b a) (b c) *
      (∑ σ : E →+* ℂ, (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re =
      (∑ σ : E →+* ℂ, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re := by
    intro a c
    rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  simp_rw [e]
  simp_rw [← Complex.re_sum]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, sum_comp]
  simp [LinearMap.flip_apply]

/- English proof (translation)
Establish `hsum : β = ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) / 2) • Pm hcj (bs b a) (bs b c)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext₂` to reduce the goal to its premises. Introduce `y z`. Establish `hP : ∀ (η ζ : Y →ₗ[ℤ] ℝ), ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z = Pf E η ζ y z` using `fun _ _ => rfl`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP, smul_eq_mul]`. Use `fock_reproducing_formula hcj b β y z` as an intermediate fact. Repeatedly rewrite using `[div_mul_eq_mul_div, ← Finset.sum_div, this]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [hsum]`.

Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem l_expand (b : Basis ι ℤ Y) (l : SymB cj Y →ₗ[ℝ] ℝ) (β : SymB cj Y) :
    l β = ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * (l (Pm hcj (bs b a) (bs b c)) / 2) := by
  have hsum : β = ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) / 2) • Pm hcj (bs b a) (bs b c) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro y z
    have hP : ∀ (η ζ : Y →ₗ[ℤ] ℝ), ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z = Pf E η ζ y z :=
      fun _ _ => rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP,
      smul_eq_mul]
    have := fock_reproducing_formula hcj b β y z
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, this]
    ring
  conv_lhs => rw [hsum]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Repro

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
