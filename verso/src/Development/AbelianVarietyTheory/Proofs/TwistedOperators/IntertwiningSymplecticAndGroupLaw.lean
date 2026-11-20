import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil.Intertw

variable {l : Type} [Fintype l]

/- English proof (translation)
Simplify using `only [sympl, pPart_smul, qPart_smul, real_inner_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_smul_left (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl (r • w) w' = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left]
  ring

/- English proof (translation)
Simplify using `only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_smul_right (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]
  ring

/- English proof (translation)
Simplify using `only [sympl, real_inner_comm (pPart w) (qPart w'), real_inner_comm (qPart w) (pPart w')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_antisymm (w w' : l ⊕ l → ℝ) : sympl w w' = -sympl w' w := by
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), real_inner_comm (qPart w) (pPart w')]
  ring

/- English proof (translation)
Establish `h1 : pPart (u - u') = pPart u - pPart u'` using `rfl`. Establish `h2 : qPart (u - u') = qPart u - qPart u'` using `rfl`. Simplify using `only [sympl, h1, h2, inner_sub_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sympl_sub_left (u u' z : l ⊕ l → ℝ) : sympl (u - u') z = sympl u z - sympl u' z := by
  have h1 : pPart (u - u') = pPart u - pPart u' := rfl
  have h2 : qPart (u - u') = qPart u - qPart u' := rfl
  simp only [sympl, h1, h2, inner_sub_left]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `hD`. Use `h D⁻¹` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at this`.
-/
theorem eq_zero_of_exp_eq_one (D : ℝ) (h : ∀ r : ℝ, exp (((π * (r * D) : ℝ) : ℂ) * I) = 1) : D = 0 := by
  by_contra hD
  have := h D⁻¹
  rw [inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I] at this
  norm_num at this

/- English proof (translation)
Simplify using `only [rhoFun, neg_add_cancel, GroundTheory.Global.gaussianSchwartz_apply]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Introduce `h`. Use `norm_phase w (-pPart w)` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `zero_ne_one this`. Simplify using the standard rewrite rules.
-/
theorem rhoFun_gaussian_ne_zero (w : l ⊕ l → ℝ) :
    rhoFun w ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) (-pPart w) ≠ 0 := by
  simp only [rhoFun, neg_add_cancel, GroundTheory.Global.gaussianSchwartz_apply]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := norm_phase w (-pPart w)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem coe_smul_sch (c : ℂ) (f : Sch l) : ⇑(c • f) = c • ⇑f := by
  funext x
  simp

/- English proof (translation)
Use `congrFun h x` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Conclude with `mul_right_cancel₀ hx this`.
-/
theorem eq_of_smul_eq_smul {c c' : ℂ} {F : EuclideanSpace ℝ l → ℂ} {x : EuclideanSpace ℝ l} (hx : F x ≠ 0)
    (h : c • F = c' • F) : c = c' := by
  have := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this

/- English proof (translation)
Use `set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0`. Establish `key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1`. Introduce `z`. Take `⟨g1, hg1⟩` from `exists_schwartz_rhoFun l z g0`. Establish `h1` using `h g1`.

Rewrite `h1` using `[hg1, rhoFun_rhoFun, rhoFun_rhoFun]`. Establish `h2` using `congrArg (rhoFun z) (h g0)`. Rewrite `h2` using `[rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u']`. Use `set a := sympl u z`. Use `set b := sympl u' z`.

Use `set F := rhoFun (u + z) ⇑g0`. Use `set G := rhoFun (u' + z) ⇑g0`. Establish `h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F = (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F`. Rewrite using `[mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]`. Establish `h4` using `eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3`.

Rewrite `h4` using `[← Complex.exp_add, ← Complex.exp_add]`. Rewrite using `[sympl_sub_left]`. Establish `e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I = (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]`. Establish `hz : ∀ z, sympl (u - u') z = 0`. Introduce `z`. Use `eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by` as an intermediate fact. Use `key (r • z)` as an intermediate fact.

Rewrite `this` using `[sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring]`. Then use the resulting hypothesis. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJ : Matrix.J l ℝ *ᵥ (u - u') = 0`. Use extensionality with `b`. Use `hz (Pi.single b 1)` as an intermediate fact.

Rewrite `this` using `[sympl_antisymm, sympl_single]`. Simplify using `using this`. Establish `hd : u - u' = 0`. Establish `: u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u'))`. Rewrite using `[Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]`.

Rewrite using `[this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]`. Conclude with `sub_eq_zero.mp hd`.
-/
theorem eq_of_rhoFun_eq {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by
  classical
  set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
  have key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1 := by
    intro z
    obtain ⟨g1, hg1⟩ := exists_schwartz_rhoFun l z g0
    have h1 := h g1
    rw [hg1, rhoFun_rhoFun, rhoFun_rhoFun] at h1
    have h2 := congrArg (rhoFun z) (h g0)
    rw [rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u'] at h2
    set a := sympl u z
    set b := sympl u' z
    set F := rhoFun (u + z) ⇑g0
    set G := rhoFun (u' + z) ⇑g0
    have h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F =
        (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F := by
      rw [mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]
    have h4 := eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    rw [sympl_sub_left]
    have e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I =
        (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]
  have hz : ∀ z, sympl (u - u') z = 0 := by
    intro z
    have := eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by
      have := key (r • z)
      rwa [sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring] at this
    linarith
  have hJ : Matrix.J l ℝ *ᵥ (u - u') = 0 := by
    ext b
    have := hz (Pi.single b 1)
    rw [sympl_antisymm, sympl_single] at this
    simpa using this
  have hd : u - u' = 0 := by
    have : u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u')) := by
      rw [Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    rw [this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]
  exact sub_eq_zero.mp hd

end GlobalTheory.RealWeil.Intertw

namespace GlobalTheory.RealWeil

open Intertw in

/- English proof (translation)
Introduce `l _ A T hadd h0 hI _`. Establish `hsurj : ∀ t (h : Sch l), T t (T (-t) h) = h` using `fun t h => by rw [← hadd, add_neg_cancel, h0]`. Use `⟨fun t w w' => ?_, fun s t w => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `hE : ∀ v v' : l ⊕ l → ℝ, exp (((π * sympl (A t v) (A t v') : ℝ) : ℂ) * I) = exp (((π * sympl v v' : ℝ) : ℂ) * I)`. Introduce `v v'`.

Use `set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0`. Take `⟨f₁, hf₁⟩` from `exists_schwartz_rhoFun l v' (T (-t) g0)`. Take `⟨f₂, hf₂⟩` from `exists_schwartz_rhoFun l v f₁`. Take `⟨f₃, hf₃⟩` from `exists_schwartz_rhoFun l (v + v') (T (-t) g0)`. Establish `e2 : f₂ = exp (((π * sympl v v' : ℝ) : ℂ) * I) • f₃`.

Apply `DFunLike.coe_injective` to reduce the goal to its premises. Rewrite using `[coe_smul_sch, hf₂, hf₁, hf₃, rhoFun_rhoFun]`. Establish `k1` using `hI t v' (T (-t) g0) f₁ hf₁`. Establish `k2` using `hI t v f₁ f₂ hf₂`. Establish `k3` using `hI t (v + v') (T (-t) g0) f₃ hf₃`.

Rewrite `k1`, `k3` using `[hsurj]`. Rewrite `k2` using `[k1, rhoFun_rhoFun, e2, map_smul, coe_smul_sch, k3, map_add]`. Conclude with `(eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (A t v + A t v')) k2).symm`. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Use `eq_zero_of_exp_eq_one _ fun r => ?_` and prove the remaining obligations.

Use `hE (r • w) w'` as an intermediate fact. Rewrite `this` using `[map_smul, sympl_smul_left, sympl_smul_left]`. Rewrite using `[show ((π * (r * (sympl (A t w) (A t w') - sympl w w')) : ℝ) : ℂ) * I = ((π * (r * sympl (A t w) (A t w')) : ℝ) : ℂ) * I - ((π * (r * sympl w w') : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_sub, this, div_self (exp_ne_zero _)]`. Apply `Intertw.eq_of_rhoFun_eq` to reduce the goal to its premises. Introduce `g`.

Take `⟨f₁, hf₁⟩` from `exists_schwartz_rhoFun l w (T (-(s + t)) g)`. Establish `h1` using `hI (s + t) w _ f₁ hf₁`. Establish `h2` using `hI t w _ f₁ hf₁`. Establish `h3` using `hI s (A t w) _ _ h2`. Rewrite `h1` using `[hsurj]`.

Rewrite `h3` using `[← hadd, ← hadd, hsurj, h1]`. Conclude with `h3`. Apply `Intertw.eq_of_rhoFun_eq` to reduce the goal to its premises. Introduce `g`. Take `⟨f₁, hf₁⟩` from `exists_schwartz_rhoFun l w g`.

Establish `h` using `hI 0 w g f₁ hf₁`. Rewrite `h` using `[h0, h0]`. Rewrite using `[← h, hf₁]`.
-/
theorem intertwining_symplectic_and_group_law : ∀ (l : Type) [Fintype l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l),
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  intro l _ A T hadd h0 hI _
  have hsurj : ∀ t (h : Sch l), T t (T (-t) h) = h := fun t h => by rw [← hadd, add_neg_cancel, h0]
  refine ⟨fun t w w' => ?_, fun s t w => ?_, fun w => ?_⟩
  · have hE : ∀ v v' : l ⊕ l → ℝ, exp (((π * sympl (A t v) (A t v') : ℝ) : ℂ) * I) =
        exp (((π * sympl v v' : ℝ) : ℂ) * I) := by
      intro v v'
      set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
      obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l v' (T (-t) g0)
      obtain ⟨f₂, hf₂⟩ := exists_schwartz_rhoFun l v f₁
      obtain ⟨f₃, hf₃⟩ := exists_schwartz_rhoFun l (v + v') (T (-t) g0)
      have e2 : f₂ = exp (((π * sympl v v' : ℝ) : ℂ) * I) • f₃ := by
        apply DFunLike.coe_injective
        rw [coe_smul_sch, hf₂, hf₁, hf₃, rhoFun_rhoFun]
      have k1 := hI t v' (T (-t) g0) f₁ hf₁
      have k2 := hI t v f₁ f₂ hf₂
      have k3 := hI t (v + v') (T (-t) g0) f₃ hf₃
      rw [hsurj] at k1 k3
      rw [k1, rhoFun_rhoFun, e2, map_smul, coe_smul_sch, k3, map_add] at k2
      exact (eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (A t v + A t v')) k2).symm
    apply sub_eq_zero.mp
    refine eq_zero_of_exp_eq_one _ fun r => ?_
    have := hE (r • w) w'
    rw [map_smul, sympl_smul_left, sympl_smul_left] at this
    rw [show ((π * (r * (sympl (A t w) (A t w') - sympl w w')) : ℝ) : ℂ) * I =
        ((π * (r * sympl (A t w) (A t w')) : ℝ) : ℂ) * I - ((π * (r * sympl w w') : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_sub, this, div_self (exp_ne_zero _)]
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w (T (-(s + t)) g)
    have h1 := hI (s + t) w _ f₁ hf₁
    have h2 := hI t w _ f₁ hf₁
    have h3 := hI s (A t w) _ _ h2
    rw [hsurj] at h1
    rw [← hadd, ← hadd, hsurj, h1] at h3
    exact h3
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w g
    have h := hI 0 w g f₁ hf₁
    rw [h0, h0] at h
    rw [← h, hf₁]

end GlobalTheory.RealWeil
