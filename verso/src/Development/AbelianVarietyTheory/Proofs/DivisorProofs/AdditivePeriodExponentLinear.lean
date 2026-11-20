import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.HalfPeriodChar

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [per, Pi.add_apply, vecMul, dotProduct, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_add' {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per τ (x + y) = per τ x + per τ y := by
  ext i
  simp only [per, Pi.add_apply, vecMul, dotProduct, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]
  ring

/- English proof (translation)
Establish `hint : ∀ l ∈ stdLat g, ∀ b ∈ U, ∃ n : ℤ, a b ⬝ᵥ per (τ b) l = 4 * π * Complex.I * s l b + n * (2 * π * Complex.I)` using `fun l hl b hb => Complex.exp_eq_exp_iff_exists_int.1 (hexp l hl b hb)`. Establish `h2pi : (2 * π * Complex.I) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Break down `U.eq_empty_or_nonempty with hUe | ⟨b0, hb0⟩` into its components or cases. Apply the tactic sequence `refine ⟨0, ?_, ?_, ?_⟩ <;> simp [cov, hUe, differentiableOn_empty]`. Use `set c : Fl g → ℂ := fun l => (a b0 ⬝ᵥ per (τ b0) l - 4 * π * Complex.I * s l b0) / (2 * π * Complex.I) with hc`.

Establish `hconst : ∀ l ∈ stdLat g, ∀ b ∈ U, a b ⬝ᵥ per (τ b) l = 4 * π * Complex.I * s l b + c l * (2 * π * Complex.I)`. Introduce `l hl`. Use `set f : E → ℂ := fun b => (a b ⬝ᵥ per (τ b) l - 4 * π * Complex.I * s l b) / (2 * π * Complex.I) with hfdef`. Establish `hf : ContinuousOn f U`. Establish `hac : ∀ i, ContinuousOn (fun b => a b i) U` using `fun i => (continuous_apply i).comp_continuousOn ha.continuousOn`.

Establish `htc : ∀ i j, ContinuousOn (fun b => τ b i j) U` using `fun i j => (hτ.2.1 i j).continuousOn`. Use `hs l hl` as an intermediate fact. Simplify using `only [hfdef, dotProduct, per, vecMul, Pi.add_apply]`. Use `fun_prop`. Set `m : E → ℤ` to `fun b => if hb : b ∈ U then (hint l hl b hb).choose else 0`.

Establish `hm : ∀ b ∈ U, (m b : ℂ) = f b`. Introduce `b hb`. Simplify using `only [m, dif_pos hb, hfdef]`. Rewrite using `[eq_div_iff h2pi]`. Take the linear combination `-(hint l hl b hb).choose_spec`.

Establish `hmc : ContinuousOn m U`. Rewrite using `[Complex.isClosedEmbedding_intCast.isInducing.continuousOn_iff]`. Conclude with `hf.congr fun b hb => hm b hb`. Introduce `b hb`. Establish `e0` using `hU.constant hmc hb hb0`.

Establish `e1` using `hm b hb`. Establish `e2` using `hm b0 hb0`. Rewrite `e1` using `[e0, e2]`. Establish `e3 : f b = c l` using `e1.symm`. Rewrite `e3` using `[hfdef, div_eq_iff h2pi]`.

Take the linear combination `e3`. Establish `hcint : ∀ l ∈ stdLat g, ∃ n : ℤ, c l = n`. Introduce `l hl`. Take `⟨n, hn⟩` from `hint l hl b0 hb0`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc]`. Simplify using `only`. Rewrite using `[div_eq_iff h2pi]`. Take the linear combination `hn`. Establish `hcadd : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c (l + l') = c l + c l'`.

Introduce `l hl l' hl'`. Simplify using `only [hc, per_add', dotProduct_add, hadd l hl l' hl' b0 hb0]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `set e : Fin g ⊕ Fin g → Fl g := fun j => Pi.basisFun ℝ (Fin g ⊕ Fin g) j with he`.

Establish `hemem : ∀ j, e j ∈ stdLat g` using `fun j => Submodule.subset_span ⟨j, rfl⟩`. Set `F : stdLat g →+ ℂ` to `AddMonoidHom.mk' (fun l => c l.1) fun l l' => hcadd l.1 l.2 l'.1 l'.2`. Establish `hcl : ∀ l ∈ stdLat g, c l = ∑ j, (l j : ℂ) * c (e j)`. Introduce `l hl`. Establish `hz : ∀ i, ∃ k : ℤ, l i = k`.

Introduce `i`. Take `⟨k, hk⟩` from `((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i`. Conclude with `⟨k, by simpa using hk.symm⟩`. Use `choose n hn using hz`. Establish `hsum : (⟨l, hl⟩ : stdLat g) = ∑ j, n j • (⟨e j, hemem j⟩ : stdLat g)`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `only [he, Pi.basisFun_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hn]`. Use `congrArg F hsum` as an intermediate fact. Simplify using `only [map_sum, map_zsmul] at this`.

Simplify using `only [F, AddMonoidHom.mk'_apply] at this`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hn j, zsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hre : ∀ j, (((c (e j)).re : ℝ) : ℂ) = c (e j)`. Introduce `j`. Take `⟨n, hn⟩` from `hcint (e j) (hemem j)`. Rewrite using `[hn]`.

Simplify using the standard rewrite rules. Set `x : Fl g` to `Sum.elim (fun i => -(c (e (Sum.inr i))).re / 2) (fun i => (c (e (Sum.inl i))).re / 2)`. Establish `hriem : ∀ l ∈ stdLat g, (riem x l : ℂ) = c l / 2`. Introduce `l hl`. Rewrite using `[hcl l hl, Fintype.sum_sum_type, add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]`.

Simplify using `only [riem, x, Sum.elim_inl, Sum.elim_inr]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hre, hre]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨x, ?_, fun P _ => Complex.exp_ne_zero _, ?_⟩` and prove the remaining obligations. Establish `ha' : DifferentiableOn ℂ (fun P : Pt E g => a P.1) (cov U g)` using `ha.comp differentiableOn_fst fun P hP => hP.1`. Establish `hai : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => a P.1 i) (cov U g)` using `fun i => (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).differentiable.comp_differentiableOn ha'`. Establish `hzi : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => P.2 i) (cov U g)` using `fun i => Differentiable.differentiableOn (by fun_prop)`. Simplify using `only [dotProduct]`.

Establish `hsum : DifferentiableOn ℂ (fun P : Pt E g => ∑ i, a P.1 i * P.2 i) (cov U g)` using `DifferentiableOn.fun_sum fun i _ => (hai i).mul (hzi i)`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(hsum.mul_const _).cexp`. Introduce `l hl P hP`. Simplify using `only [transl]`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add, dotProduct_add, hconst l hl P.1 hP.1, hriem l hl]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flat_of_exp_eq {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap U τ) (hU : IsPreconnected U) (s : Fl g → E → ℂ) (a : E → Fin g → ℂ)
    (hs : ∀ l ∈ stdLat g, ContinuousOn (s l) U)
    (hadd : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, s (l + l') b = s l b + s l' b)
    (ha : DifferentiableOn ℂ a U)
    (hexp : ∀ l ∈ stdLat g, ∀ b ∈ U,
      Complex.exp (a b ⬝ᵥ per (τ b) l) = Complex.exp (4 * π * Complex.I * s l b)) :
    ∃ x : Fl g, IsBundleIso U τ (stdLat g)
      (fun l _ => Complex.exp (2 * π * Complex.I * (-(riem x l : ℂ))))
      (fun l P => Complex.exp (2 * π * Complex.I * s l P.1))
      (fun P => Complex.exp (a P.1 ⬝ᵥ P.2 / 2)) := by
  have hint : ∀ l ∈ stdLat g, ∀ b ∈ U, ∃ n : ℤ,
      a b ⬝ᵥ per (τ b) l = 4 * π * Complex.I * s l b + n * (2 * π * Complex.I) :=
    fun l hl b hb => Complex.exp_eq_exp_iff_exists_int.1 (hexp l hl b hb)
  have h2pi : (2 * π * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases U.eq_empty_or_nonempty with hUe | ⟨b0, hb0⟩
  · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [cov, hUe, differentiableOn_empty]
  set c : Fl g → ℂ := fun l =>
    (a b0 ⬝ᵥ per (τ b0) l - 4 * π * Complex.I * s l b0) / (2 * π * Complex.I) with hc
  have hconst : ∀ l ∈ stdLat g, ∀ b ∈ U,
      a b ⬝ᵥ per (τ b) l = 4 * π * Complex.I * s l b + c l * (2 * π * Complex.I) := by
    intro l hl
    set f : E → ℂ := fun b =>
      (a b ⬝ᵥ per (τ b) l - 4 * π * Complex.I * s l b) / (2 * π * Complex.I) with hfdef
    have hf : ContinuousOn f U := by
      have hac : ∀ i, ContinuousOn (fun b => a b i) U := fun i =>
        (continuous_apply i).comp_continuousOn ha.continuousOn
      have htc : ∀ i j, ContinuousOn (fun b => τ b i j) U := fun i j =>
        (hτ.2.1 i j).continuousOn
      have := hs l hl
      simp only [hfdef, dotProduct, per, vecMul, Pi.add_apply]
      fun_prop
    classical
    let m : E → ℤ := fun b => if hb : b ∈ U then (hint l hl b hb).choose else 0
    have hm : ∀ b ∈ U, (m b : ℂ) = f b := by
      intro b hb
      simp only [m, dif_pos hb, hfdef]
      rw [eq_div_iff h2pi]
      linear_combination -(hint l hl b hb).choose_spec
    have hmc : ContinuousOn m U := by
      rw [Complex.isClosedEmbedding_intCast.isInducing.continuousOn_iff]
      exact hf.congr fun b hb => hm b hb
    intro b hb
    have e0 := hU.constant hmc hb hb0
    have e1 := hm b hb
    have e2 := hm b0 hb0
    rw [e0, e2] at e1
    have e3 : f b = c l := e1.symm
    rw [hfdef, div_eq_iff h2pi] at e3
    linear_combination e3

  have hcint : ∀ l ∈ stdLat g, ∃ n : ℤ, c l = n := by
    intro l hl
    obtain ⟨n, hn⟩ := hint l hl b0 hb0
    refine ⟨n, ?_⟩
    rw [hc]
    simp only
    rw [div_eq_iff h2pi]
    linear_combination hn
  have hcadd : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c (l + l') = c l + c l' := by
    intro l hl l' hl'
    simp only [hc, per_add', dotProduct_add, hadd l hl l' hl' b0 hb0]
    field_simp
    ring
  set e : Fin g ⊕ Fin g → Fl g := fun j => Pi.basisFun ℝ (Fin g ⊕ Fin g) j with he
  have hemem : ∀ j, e j ∈ stdLat g := fun j => Submodule.subset_span ⟨j, rfl⟩
  let F : stdLat g →+ ℂ := AddMonoidHom.mk' (fun l => c l.1) fun l l' => hcadd l.1 l.2 l'.1 l'.2
  have hcl : ∀ l ∈ stdLat g, c l = ∑ j, (l j : ℂ) * c (e j) := by
    intro l hl
    have hz : ∀ i, ∃ k : ℤ, l i = k := by
      intro i
      obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
      exact ⟨k, by simpa using hk.symm⟩
    choose n hn using hz
    have hsum : (⟨l, hl⟩ : stdLat g) = ∑ j, n j • (⟨e j, hemem j⟩ : stdLat g) := by
      apply Subtype.ext
      ext i
      simp only [he, Pi.basisFun_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
        Finset.sum_apply, Pi.smul_apply, Pi.single_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hn]
    have := congrArg F hsum
    simp only [map_sum, map_zsmul] at this
    simp only [F, AddMonoidHom.mk'_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hn j, zsmul_eq_mul]
    push_cast
    ring
  have hre : ∀ j, (((c (e j)).re : ℝ) : ℂ) = c (e j) := by
    intro j
    obtain ⟨n, hn⟩ := hcint (e j) (hemem j)
    rw [hn]
    simp
  let x : Fl g := Sum.elim (fun i => -(c (e (Sum.inr i))).re / 2) (fun i => (c (e (Sum.inl i))).re / 2)
  have hriem : ∀ l ∈ stdLat g, (riem x l : ℂ) = c l / 2 := by
    intro l hl
    rw [hcl l hl, Fintype.sum_sum_type, add_div, Finset.sum_div, Finset.sum_div,
      ← Finset.sum_add_distrib]
    simp only [riem, x, Sum.elim_inl, Sum.elim_inr]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hre, hre]
    ring
  refine ⟨x, ?_, fun P _ => Complex.exp_ne_zero _, ?_⟩
  · have ha' : DifferentiableOn ℂ (fun P : Pt E g => a P.1) (cov U g) :=
      ha.comp differentiableOn_fst fun P hP => hP.1
    have hai : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => a P.1 i) (cov U g) := fun i =>
      (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).differentiable.comp_differentiableOn ha'
    have hzi : ∀ i, DifferentiableOn ℂ (fun P : Pt E g => P.2 i) (cov U g) := fun i =>
      Differentiable.differentiableOn (by fun_prop)
    simp only [dotProduct]
    have hsum : DifferentiableOn ℂ (fun P : Pt E g => ∑ i, a P.1 i * P.2 i) (cov U g) :=
      DifferentiableOn.fun_sum fun i _ => (hai i).mul (hzi i)
    simp only [div_eq_mul_inv]
    exact (hsum.mul_const _).cexp
  · intro l hl P hP
    simp only [transl]
    rw [← Complex.exp_add, ← Complex.exp_add, dotProduct_add, hconst l hl P.1 hP.1, hriem l hl]
    congr 1
    ring

end GlobalTheory.HalfPeriodChar
