import Mathlib

open Polynomial

namespace GlobalTheory.CompanionTheory.ConstCoeffODE

noncomputable def op (c : ℂ) (y : ℝ → ℂ) : ℝ → ℂ := deriv y - c • y

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h : deriv (a + b) t = deriv a t + deriv b t` using `((ha t).hasDerivAt.add (hb t).hasDerivAt).deriv`. Simplify using `only [op, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem op_add (c : ℂ) {a b : ℝ → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    op c (a + b) = op c a + op c b := by
  funext t
  have h : deriv (a + b) t = deriv a t + deriv b t :=
    ((ha t).hasDerivAt.add (hb t).hasDerivAt).deriv
  simp only [op, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h : deriv (k • a) t = k • deriv a t` using `((ha t).hasDerivAt.const_smul k).deriv`. Simplify using `only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem op_smul (c k : ℂ) {a : ℝ → ℂ} (ha : Differentiable ℝ a) :
    op c (k • a) = k • op c a := by
  funext t
  have h : deriv (k • a) t = k • deriv a t :=
    ((ha t).hasDerivAt.const_smul k).deriv
  simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

noncomputable def step (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) where
  carrier := {y | Differentiable ℝ y ∧ op c y ∈ S}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, by rw [op_add c ha hb]; exact S.add_mem ha' hb'⟩
  zero_mem' := by
    refine ⟨differentiable_const (0 : ℂ), ?_⟩
    have : op c (0 : ℝ → ℂ) = 0 := by
      funext t
      simp [op]
    rw [this]
    exact S.zero_mem
  smul_mem' := by
    rintro k a ⟨ha, ha'⟩
    exact ⟨ha.const_smul k, by rw [op_smul c k ha]; exact S.smul_mem k ha'⟩

noncomputable def stepMap (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : step c S →ₗ[ℂ] S × ℂ where
  toFun y := (⟨op c y.1, y.2.2⟩, y.1 0)
  map_add' a b := by
    ext1
    · exact Subtype.ext (op_add c a.2.1 b.2.1)
    · rfl
  map_smul' k a := by
    ext1
    · exact Subtype.ext (op_smul c k a.2.1)
    · rfl

/- English proof (translation)
Establish `hd : ∀ t, deriv y t = c * y t`. Introduce `t`. Use `congrFun h t` as an intermediate fact. Simplify using `only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Conclude with `sub_eq_zero.mp this`.

Establish `he : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * (s : ℂ))) (Complex.exp (-c * (t : ℂ)) * (-c)) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c) t`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)`. Conclude with `h1.cexp`.

Establish `hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y s * Complex.exp (-c * (s : ℂ))) 0 t`. Introduce `t`. Establish `h2` using `(hy t).hasDerivAt.mul (he t)`. Establish `h3 : deriv y t * Complex.exp (-c * (t : ℂ)) + y t * (Complex.exp (-c * (t : ℂ)) * (-c)) = 0`. Rewrite using `[hd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Conclude with `h2`. Establish `hc` using `is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv)`. Use function extensionality and compare the values at `t`.

Use `hc t 0` as an intermediate fact. Simplify using `only [h0, zero_mul] at this`. Simplify `this` using `[Complex.exp_ne_zero]`.
-/
theorem eq_zero_of_op_eq_zero (c : ℂ) {y : ℝ → ℂ} (hy : Differentiable ℝ y)
    (h : op c y = 0) (h0 : y 0 = 0) : y = 0 := by
  have hd : ∀ t, deriv y t = c * y t := by
    intro t
    have := congrFun h t
    simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  have he : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * (s : ℂ)))
      (Complex.exp (-c * (t : ℂ)) * (-c)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)
    exact h1.cexp
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y s * Complex.exp (-c * (s : ℂ))) 0 t := by
    intro t
    have h2 := (hy t).hasDerivAt.mul (he t)
    have h3 : deriv y t * Complex.exp (-c * (t : ℂ)) + y t * (Complex.exp (-c * (t : ℂ)) * (-c)) = 0 := by
      rw [hd]; ring
    rw [h3] at h2
    exact h2
  have hc := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv)
  funext t
  have := hc t 0
  simp only [h0, zero_mul] at this
  simpa [Complex.exp_ne_zero] using this

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `h1 : op c y.1 = 0` using `congrArg (fun p : S × ℂ => (p.1 : ℝ → ℂ)) hy`. Establish `h2 : y.1 0 = 0` using `congrArg Prod.snd hy`. Conclude with `Subtype.ext (eq_zero_of_op_eq_zero c y.2.1 h1 h2)`.
-/
theorem stepMap_injective (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) :
    Function.Injective (stepMap c S) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : op c y.1 = 0 := congrArg (fun p : S × ℂ => (p.1 : ℝ → ℂ)) hy
  have h2 : y.1 0 = 0 := congrArg Prod.snd hy
  exact Subtype.ext (eq_zero_of_op_eq_zero c y.2.1 h1 h2)

/- English proof (translation)
The claim follows from `FiniteDimensional.of_injective (stepMap c S) (stepMap_injective c S)`.
-/
theorem step_finite (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (step c S) :=
  FiniteDimensional.of_injective (stepMap c S) (stepMap_injective c S)

/- English proof (translation)
Establish `h` using `LinearMap.finrank_le_finrank_of_injective (stepMap_injective c S)`. Rewrite `h` using `[Module.finrank_prod, Module.finrank_self]`. Conclude with `h`.
-/
theorem step_finrank_le (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    Module.finrank ℂ (step c S) ≤ Module.finrank ℂ S + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (stepMap_injective c S)
  rw [Module.finrank_prod, Module.finrank_self] at h
  exact h

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Use `⟨⊥, inferInstance, by simp, ?_⟩` and prove the remaining obligations. Introduce `X _ _ D ev _ x hx`.

Simplify using `using hx`. Consider the case `cons c l ih`. Take `⟨S, hfin, hrank, hS⟩` from `ih`. Use `⟨step c S, step_finite c S, ?_, ?_⟩` and prove the remaining obligations. Use `step_finrank_le c S` as an intermediate fact.

Simplify using `only [List.length_cons]`. Use linear arithmetic over natural numbers and integers. Introduce `X _ _ D ev hD x hx set Q : Module.End ℂ X := D - c • (1 : Module.End ℂ X) with hQ set P : Module.End ℂ X := (l.map fun c => D - c • (1 : Module.End ℂ X)).prod with hP`. Establish `hcomm : Commute Q P`. Use `Commute.list_prod_right _ _ ?_` and prove the remaining obligations.

Introduce `z hz`. Take `⟨b, -, rfl⟩` from `List.mem_map.mp hz`. Establish `hD1 : Commute D (1 : Module.End ℂ X)` using `Commute.one_right D`. Conclude with `((Commute.refl D).sub_right (hD1.smul_right b)).sub_left ((hD1.symm.sub_right ((Commute.one_left _).smul_right b)).smul_left c)`. Establish `h1 : ev (P (Q x)) = 0`.

Establish `h2 : (Q * P) x = (P * Q) x` using `by rw [hcomm.eq]`. Establish `h3 : ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod) = P` using `rfl`. Simplify using `only [List.map_cons, List.prod_cons] at hx`. Rewrite `hx` using `[h3]`. Establish `h4 : (P * Q) x = P (Q x)` using `rfl`.

Rewrite using `[← h4, ← h2]`. Conclude with `hx`. Establish `h5 : ev (Q x) ∈ S` using `hS X D ev hD (Q x) h1`. Establish `hdiff : Differentiable ℝ (ev x)` using `fun t => (hD x t).differentiableAt`. Use `⟨hdiff, ?_⟩` and prove the remaining obligations.

Establish `h6 : op c (ev x) = ev (Q x)`. Use function extensionality and compare the values at `t`. Simplify using `[op, hQ, (hD x t).deriv]`. Rewrite using `[h6]`. Conclude with `h5`.
-/
theorem solutions_mem_finite :
    ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
        (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) →
          ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by
  intro l
  induction l with
  | nil =>
    refine ⟨⊥, inferInstance, by simp, ?_⟩
    intro X _ _ D ev _ x hx
    simpa using hx
  | cons c l ih =>
    obtain ⟨S, hfin, hrank, hS⟩ := ih
    refine ⟨step c S, step_finite c S, ?_, ?_⟩
    · have := step_finrank_le c S
      simp only [List.length_cons]
      omega
    · intro X _ _ D ev hD x hx
      set Q : Module.End ℂ X := D - c • (1 : Module.End ℂ X) with hQ
      set P : Module.End ℂ X := (l.map fun c => D - c • (1 : Module.End ℂ X)).prod with hP
      have hcomm : Commute Q P := by
        refine Commute.list_prod_right _ _ ?_
        intro z hz
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hz
        have hD1 : Commute D (1 : Module.End ℂ X) := Commute.one_right D
        exact ((Commute.refl D).sub_right (hD1.smul_right b)).sub_left
          ((hD1.symm.sub_right ((Commute.one_left _).smul_right b)).smul_left c)
      have h1 : ev (P (Q x)) = 0 := by
        have h2 : (Q * P) x = (P * Q) x := by rw [hcomm.eq]
        have h3 : ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod) = P := rfl
        simp only [List.map_cons, List.prod_cons] at hx
        rw [h3] at hx
        have h4 : (P * Q) x = P (Q x) := rfl
        rw [← h4, ← h2]
        exact hx
      have h5 : ev (Q x) ∈ S := hS X D ev hD (Q x) h1
      have hdiff : Differentiable ℝ (ev x) := fun t => (hD x t).differentiableAt
      refine ⟨hdiff, ?_⟩
      have h6 : op c (ev x) = ev (Q x) := by
        funext t
        simp [op, hQ, (hD x t).deriv]
      rw [h6]
      exact h5

end GlobalTheory.CompanionTheory.ConstCoeffODE
