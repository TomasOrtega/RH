import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.DomZ

open Matrix

def quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

/- English proof (translation)
Simplify using `only [quadOf, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadOf_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadOf A x = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [quadOf, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Unfold `quadOf`. Use `fun_prop`.
-/
theorem continuous_quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadOf A) := by
  unfold quadOf
  fun_prop

/- English proof (translation)
Simplify using `only [quadOf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quadOf_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    quadOf A (t • x) = t ^ 2 * quadOf A x := by
  simp only [quadOf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hpos : ∀ x, x ≠ 0 → 0 < quadOf P x` using `fun x hx => by`. Rewrite using `[quadOf_eq]`. Conclude with `hP.dotProduct_mulVec_pos hx`. Establish `hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1)` using `isCompact_sphere 0 1`. Establish `hne : ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1, u ≠ 0` using `fun u hu h => by`.

Simplify using `[h] at hu`. Establish `hc : ContinuousOn (fun u => quadOf R u / quadOf P u) (Metric.sphere (0 : Fin n → ℝ) 1)` using `(continuous_quadOf R).continuousOn.div (continuous_quadOf P).continuousOn fun u hu => (hpos u (hne u hu)).ne'`. Take `⟨K, hK⟩` from `hS.bddAbove_image hc`. Use `⟨⌈K⌉₊, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using `[quadOf]`. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.2 hx`. Take `⟨u, hu⟩ : ∃ u, u = ‖x‖⁻¹ • x` from `⟨_, rfl⟩`. Establish `hum : u ∈ Metric.sphere (0 : Fin n → ℝ) 1`.

Simplify using `[hu, norm_smul, hn]`. Establish `h1 : quadOf R u / quadOf P u ≤ K` using `hK ⟨u, hum, rfl⟩`. Establish `hpu` using `hpos u (hne u hum)`. Establish `h2 : quadOf R u ≤ ⌈K⌉₊ * quadOf P u`. Rewrite `h1` using `[div_le_iff₀ hpu]`.

Conclude with `h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hpu.le)`. Establish `hxu : x = ‖x‖ • u` using `by simp [hu, smul_smul, hn]`. Establish `eR : ∀ A : Matrix (Fin n) (Fin n) ℝ, quadOf A x = ‖x‖ ^ 2 * quadOf A u` using `fun A => by`. Rewrite using `[← quadOf_smul, ← hxu]`. Rewrite using `[eR, eR]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_nat_quadOf_le {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ) : ∃ C : ℕ, ∀ x, quadOf R x ≤ C * quadOf P x := by
  have hpos : ∀ x, x ≠ 0 → 0 < quadOf P x := fun x hx => by
    rw [quadOf_eq]
    exact hP.dotProduct_mulVec_pos hx
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne : ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1, u ≠ 0 := fun u hu h => by
    simp [h] at hu
  have hc : ContinuousOn (fun u => quadOf R u / quadOf P u) (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (continuous_quadOf R).continuousOn.div (continuous_quadOf P).continuousOn
      fun u hu => (hpos u (hne u hu)).ne'
  obtain ⟨K, hK⟩ := hS.bddAbove_image hc
  refine ⟨⌈K⌉₊, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp [quadOf]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  obtain ⟨u, hu⟩ : ∃ u, u = ‖x‖⁻¹ • x := ⟨_, rfl⟩
  have hum : u ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [hu, norm_smul, hn]
  have h1 : quadOf R u / quadOf P u ≤ K := hK ⟨u, hum, rfl⟩
  have hpu := hpos u (hne u hum)
  have h2 : quadOf R u ≤ ⌈K⌉₊ * quadOf P u := by
    rw [div_le_iff₀ hpu] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hpu.le)
  have hxu : x = ‖x‖ • u := by simp [hu, smul_smul, hn]
  have eR : ∀ A : Matrix (Fin n) (Fin n) ℝ, quadOf A x = ‖x‖ ^ 2 * quadOf A u := fun A => by
    rw [← quadOf_smul, ← hxu]
  rw [eR, eR]
  calc ‖x‖ ^ 2 * quadOf R u ≤ ‖x‖ ^ 2 * (⌈K⌉₊ * quadOf P u) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

/- English proof (translation)
Establish `h` using `(hA.hadamard hG).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))`. Simplify `h` using `[dotProduct, mulVec, Matrix.hadamard_apply]`.
-/
theorem sum_mul_nonneg {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * G i j := by
  have h := (hA.hadamard hG).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply] using h

/- English proof (translation)
Establish `hrat : ∀ w : Fin n → ℚ, 0 ≤ quadOf G fun i => (w i : ℝ)` using `fun w => by`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w`. Use `choose v hv using hc`. Establish `hc0 : (((c : ℤ) : ℝ)) ≠ 0`. Conclude with `nonZeroDivisors.ne_zero c.2` after adjusting the coercions.

Establish `hv' : ∀ i, (v i : ℚ) = (c : ℤ) * w i` using `fun i => by`. Simplify `hv i` using `[Algebra.smul_def]`. Establish `e : (fun i => (v i : ℝ)) = ((c : ℤ) : ℝ) • fun i => (w i : ℝ)`. Use function extensionality and compare the values at `i`. Use `congrArg (Rat.cast : ℚ → ℝ) (hv' i)` as an intermediate fact.

Simplify using `using this`. Establish `h1` using `h v`. Rewrite `h1` using `[e, quadOf_smul]`. Establish `h2 : 0 < (((c : ℤ) : ℝ)) ^ 2` using `by positivity`. Conclude with `nonneg_of_mul_nonneg_right h1 h2`.

Establish `hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ))` using `DenseRange.piMap (fun _ => Rat.denseRange_cast)`. Establish `hcl : IsClosed {x : Fin n → ℝ | 0 ≤ quadOf G x}` using `isClosed_le continuous_const (continuous_quadOf G)`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs fun x => ?_` and prove the remaining obligations. Rewrite using `[← quadOf_eq]`. Conclude with `hdense.induction_on (p := fun x => 0 ≤ quadOf G x) x hcl hrat`.
-/
theorem posSemidef_of_int_nonneg {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hs : G.IsHermitian)
    (h : ∀ v : Fin n → ℤ, 0 ≤ quadOf G fun i => (v i : ℝ)) : G.PosSemidef := by
  have hrat : ∀ w : Fin n → ℚ, 0 ≤ quadOf G fun i => (w i : ℝ) := fun w => by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
    choose v hv using hc
    have hc0 : (((c : ℤ) : ℝ)) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.ne_zero c.2
    have hv' : ∀ i, (v i : ℚ) = (c : ℤ) * w i := fun i => by
      simpa [Algebra.smul_def] using hv i
    have e : (fun i => (v i : ℝ)) = ((c : ℤ) : ℝ) • fun i => (w i : ℝ) := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hv' i)
      simpa using this
    have h1 := h v
    rw [e, quadOf_smul] at h1
    have h2 : 0 < (((c : ℤ) : ℝ)) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right h1 h2
  have hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ quadOf G x} := isClosed_le continuous_const (continuous_quadOf G)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs fun x => ?_
  rw [← quadOf_eq]
  exact hdense.induction_on (p := fun x => 0 ≤ quadOf G x) x hcl hrat

section Forms

variable {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X)

def elemForm (i j : Fin n) : LinearMap.BilinForm ℤ X :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)

/- English proof (translation)
The claim follows from `add_comm _ _`.
-/
theorem elemForm_comm (i j : Fin n) : elemForm b i j = elemForm b j i := add_comm _ _

/- English proof (translation)
Use `b.ext fun k => b.ext fun l => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]`. Simplify using `[elemForm, Finsupp.single_apply, mul_add, Finset.sum_add_distrib]`. Rewrite using `[hβ (b l) (b k)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_smul_eq {β : LinearMap.BilinForm ℤ X} (hβ : ∀ y z, β y z = β z y) :
    (2 : ℤ) • β = ∑ i, ∑ j, β (b i) (b j) • elemForm b i j := by
  refine b.ext fun k => b.ext fun l => ?_
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  simp [elemForm, Finsupp.single_apply, mul_add, Finset.sum_add_distrib]
  rw [hβ (b l) (b k)]
  ring

/- English proof (translation)
Establish `h` using `congrArg L (two_smul_eq b hβ)`. Simplify using `only [map_smul, map_sum, smul_eq_mul] at h`. Rewrite using `[h]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem two_mul_map (L : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    (hβ : ∀ y z, β y z = β z y) : 2 * L β = ∑ i, ∑ j, L (elemForm b i j) * β (b i) (b j) := by
  have h := congrArg L (two_smul_eq b hβ)
  simp only [map_smul, map_sum, smul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end Forms

end GlobalTheory.CompanionTheory.Ar.Fan.DomZ

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix DomZ

/- English proof (translation)
Introduce `ℓ m hℓ`. Set `Q : Matrix (Fin n) (Fin n) ℚ` to `fun i j => (ℓ (elemForm b i j) : ℚ)`. Set `P : Matrix (Fin n) (Fin n) ℝ` to `Q.map (Rat.cast : ℚ → ℝ)`. Set `R : Matrix (Fin n) (Fin n) ℝ` to `fun i j => (m (elemForm b i j) : ℝ)`. Establish `hQs : Q.IsSymm`.

Use extensionality with `i j`. Use `show (ℓ (elemForm b j i) : ℚ) = (ℓ (elemForm b i j) : ℚ)`. Rewrite using `[elemForm_comm b j i]`. Establish `hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j` using `fun v hv => by`. Set `l : X →ₗ[ℤ] ℤ` to `∑ i, v i • b.coord i`.

Establish `hl : ∀ i, l (b i) = v i` using `fun i => by simp [l, Finsupp.single_apply]`. Establish `hsym : ∀ y z, GlobalTheory.PolFan.sqForm l y z = GlobalTheory.PolFan.sqForm l z y` using `fun y z => by`. Simplify using `[mul_comm]`. Establish `hne : GlobalTheory.PolFan.sqForm l ≠ 0`. Introduce `h0`.

Take `⟨k, hk⟩` from `Function.ne_iff.1 hv`. Establish `h1` using `congrArg (fun β : LinearMap.BilinForm ℤ X => β (b k) (b k)) h0`. Simplify using `only [GlobalTheory.PolFan.sqForm_apply, hl, LinearMap.zero_apply, mul_self_eq_zero] at h1`. Conclude with `hk h1`. Establish `h1` using `hℓ (GlobalTheory.PolFan.sqForm l) (mem_balForms_int.2 hsym) (fun y => by simpa using mul_self_nonneg (l y)) hne`.

Establish `h2` using `two_mul_map b ℓ hsym`. Simplify using `only [GlobalTheory.PolFan.sqForm_apply, hl] at h2`. Establish `h3 : (0 : ℤ) < ∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j)`. Rewrite using `[← h2]`. Use linear arithmetic over natural numbers and integers.

Establish `h4 : ((∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) : ℤ) : ℚ) = ∑ i, ∑ j, Q i j * v i * v j`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Q]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← h4]`. Conclude with `h3` after adjusting the coercions. Establish `hP : P.PosDef` using `posDef_of_int_pos n Q hQs hQ`. Take `⟨C, hC⟩` from `exists_nat_quadOf_le hP R`. Use `⟨C, fun β hβ hp => ?_⟩` and prove the remaining obligations.

Establish `hβs` using `mem_balForms_int.1 hβ`. Set `G : Matrix (Fin n) (Fin n) ℝ` to `fun i j => (β (b i) (b j) : ℝ)`. Establish `hG : G.PosSemidef`. Use `posSemidef_of_int_nonneg ?_ fun v => ?_` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[Matrix.conjTranspose_apply, star_trivial]`. Use `show ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)`. Rewrite using `[hβs]`. Establish `h1` using `hp (∑ i, v i • b i)`. Establish `h2 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) = quadOf G fun i => (v i : ℝ)`.

Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, quadOf, G]`. Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`. Conclude with `h1` after adjusting the coercions. Establish `hRs : R.IsHermitian`.

Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, star_trivial]`. Use `show (m (elemForm b j i) : ℝ) = (m (elemForm b i j) : ℝ)`. Rewrite using `[elemForm_comm b j i]`. Establish `hA : ((C : ℝ) • P - R).PosSemidef`.

Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_` and prove the remaining obligations. Conclude with `(hP.1.smul (by simp)).sub hRs`. Rewrite using `[← quadOf_eq]`. Establish `e : quadOf ((C : ℝ) • P - R) x = C * quadOf P x - quadOf R x`. Simplify using `only [quadOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the linear relations using `[hC x]`. Establish `h1` using `sum_mul_nonneg hA hG`.

Establish `hPij : ∀ i j, P i j = (ℓ (elemForm b i j) : ℝ)` using `fun i j => by show (((ℓ (elemForm b i j) : ℤ) : ℚ) : ℝ) = _`. Simplify using the standard rewrite rules. Establish `e1 : ∑ i, ∑ j, P i j * G i j = ((2 * ℓ β : ℤ) : ℝ)`. Rewrite using `[two_mul_map b ℓ hβs]`. Use `push_cast`.

Simplify using `only [hPij, G]`. Establish `e2 : ∑ i, ∑ j, R i j * G i j = ((2 * m β : ℤ) : ℝ)`. Rewrite using `[two_mul_map b m hβs]`. Use `push_cast`. Simplify using `only [R, G]`.

Establish `e3 : ∑ i, ∑ j, ((C : ℝ) • P - R) i j * G i j = C * ∑ i, ∑ j, P i j * G i j - ∑ i, ∑ j, R i j * G i j`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e3, e1, e2]`.

Establish `h2 : (2 * m β : ℝ) ≤ C * (2 * ℓ β)`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (m β : ℝ) ≤ C * ℓ β` using `by linarith`. Conclude with `h3` after adjusting the coercions.
-/
theorem dominates_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := by
  intro ℓ m hℓ
  let Q : Matrix (Fin n) (Fin n) ℚ := fun i j => (ℓ (elemForm b i j) : ℚ)
  let P : Matrix (Fin n) (Fin n) ℝ := Q.map (Rat.cast : ℚ → ℝ)
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (m (elemForm b i j) : ℝ)
  have hQs : Q.IsSymm := by
    ext i j
    show (ℓ (elemForm b j i) : ℚ) = (ℓ (elemForm b i j) : ℚ)
    rw [elemForm_comm b j i]
  have hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := fun v hv => by
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ i, l (b i) = v i := fun i => by simp [l, Finsupp.single_apply]
    have hsym : ∀ y z, GlobalTheory.PolFan.sqForm l y z = GlobalTheory.PolFan.sqForm l z y := fun y z => by
      simp [mul_comm]
    have hne : GlobalTheory.PolFan.sqForm l ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
      have h1 := congrArg (fun β : LinearMap.BilinForm ℤ X => β (b k) (b k)) h0
      simp only [GlobalTheory.PolFan.sqForm_apply, hl, LinearMap.zero_apply, mul_self_eq_zero] at h1
      exact hk h1
    have h1 := hℓ (GlobalTheory.PolFan.sqForm l) (mem_balForms_int.2 hsym)
      (fun y => by simpa using mul_self_nonneg (l y)) hne
    have h2 := two_mul_map b ℓ hsym
    simp only [GlobalTheory.PolFan.sqForm_apply, hl] at h2
    have h3 : (0 : ℤ) < ∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) := by
      rw [← h2]
      omega
    have h4 : ((∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) : ℤ) : ℚ) = ∑ i, ∑ j, Q i j * v i * v j := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Q]
      ring
    rw [← h4]
    exact_mod_cast h3
  have hP : P.PosDef := posDef_of_int_pos n Q hQs hQ
  obtain ⟨C, hC⟩ := exists_nat_quadOf_le hP R
  refine ⟨C, fun β hβ hp => ?_⟩
  have hβs := mem_balForms_int.1 hβ
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => (β (b i) (b j) : ℝ)
  have hG : G.PosSemidef := by
    refine posSemidef_of_int_nonneg ?_ fun v => ?_
    · ext i j
      rw [Matrix.conjTranspose_apply, star_trivial]
      show ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
      rw [hβs]
    · have h1 := hp (∑ i, v i • b i)
      have h2 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) = quadOf G fun i => (v i : ℝ) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, quadOf, G]
        push_cast
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [← h2]
      exact_mod_cast h1
  have hRs : R.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    show (m (elemForm b j i) : ℝ) = (m (elemForm b i j) : ℝ)
    rw [elemForm_comm b j i]
  have hA : ((C : ℝ) • P - R).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · exact (hP.1.smul (by simp)).sub hRs
    · rw [← quadOf_eq]
      have e : quadOf ((C : ℝ) • P - R) x = C * quadOf P x - quadOf R x := by
        simp only [quadOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      linarith [hC x]
  have h1 := sum_mul_nonneg hA hG
  have hPij : ∀ i j, P i j = (ℓ (elemForm b i j) : ℝ) := fun i j => by
    show (((ℓ (elemForm b i j) : ℤ) : ℚ) : ℝ) = _
    simp
  have e1 : ∑ i, ∑ j, P i j * G i j = ((2 * ℓ β : ℤ) : ℝ) := by
    rw [two_mul_map b ℓ hβs]
    push_cast
    simp only [hPij, G]
  have e2 : ∑ i, ∑ j, R i j * G i j = ((2 * m β : ℤ) : ℝ) := by
    rw [two_mul_map b m hβs]
    push_cast
    simp only [R, G]
  have e3 : ∑ i, ∑ j, ((C : ℝ) • P - R) i j * G i j
      = C * ∑ i, ∑ j, P i j * G i j - ∑ i, ∑ j, R i j * G i j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3, e1, e2] at h1
  have h2 : (2 * m β : ℝ) ≤ C * (2 * ℓ β) := by
    push_cast at h1
    linarith
  have h3 : (m β : ℝ) ≤ C * ℓ β := by linarith
  exact_mod_cast h3

/- English proof (translation)
Introduce `X _ _ _` and use `dominates_of_basis (Module.finBasis ℤ X)`.
-/
theorem dominates_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X],
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := fun X _ _ _ => dominates_of_basis (Module.finBasis ℤ X)

end GlobalTheory.CompanionTheory.Ar.Fan
