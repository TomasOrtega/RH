import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) = fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • X))`. Use function extensionality and compare the values at `t`. Establish `: (t : ℂ) • X = t • X` using `by ext a b; simp [Complex.real_smul]`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `e2 : X i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • X) * X)`. Simplify using `[NormedSpace.exp_zero]`. Rewrite using `[e1, e2]`. Use `open scoped Matrix.Norms.Operator in`. Conclude with `(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)`.
-/
theorem entry_hasDerivAt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • X)) := by
    funext t
    have : (t : ℂ) • X = t • X := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : X i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • X) * X) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def curve : Bool × B.Mat k r → B.Mat k r → ℝ → B.Mat k r
  | (true, X), g, t => NormedSpace.exp (-((t : ℂ) • X)) * g
  | (false, X), g, t => g * NormedSpace.exp ((t : ℂ) • X)

def dir : Bool × B.Mat k r → B.Mat k r → B.Mat k r
  | (true, X), g => -(X * g)
  | (false, X), g => g * X

def act {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Bool × B.Mat k r → (B.Mat k r → E) → B.Mat k r → E
  | (true, X), f => B.LdV X f
  | (false, X), f => Formalism.REAL.RdV X f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Take `⟨b, X⟩` from `o`. Apply the tactic sequence `cases b <;> rfl`.
-/
theorem act_eq (o : Bool × B.Mat k r) (f : B.Mat k r → E) (g : B.Mat k r) :
    act o f g = deriv (fun t : ℝ => f (curve o g t)) 0 := by
  obtain ⟨b, X⟩ := o
  cases b <;> rfl

/- English proof (translation)
Take `⟨b, X⟩` from `o`. Apply the tactic sequence `cases b <;> simp [curve]`.
-/
theorem curve_zero (o : Bool × B.Mat k r) (g : B.Mat k r) : curve o g 0 = g := by
  obtain ⟨b, X⟩ := o
  cases b <;> simp [curve]

/- English proof (translation)
Break down `o with ⟨_ | _, X⟩` into its components or cases. Conclude with `UH_mul _ _ _ hg (exp_mem_UH _ _ (lie_smul _ X hX t))`. Establish `: -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X` using `by push_cast; rw [neg_smul] show NormedSpace.exp (-((t : ℂ) • X)) * g ∈ B.GV k r`. Rewrite using `[this]`. Conclude with `UH_mul _ _ _ (exp_mem_UH _ _ (lie_smul _ X hX (-t))) hg`.
-/
theorem curve_mem (o : Bool × B.Mat k r) (g : B.Mat k r) (t : ℝ) (hX : B.inLie k r o.2)
    (hg : g ∈ B.GV k r) : curve o g t ∈ B.GV k r := by
  rcases o with ⟨_ | _, X⟩
  · exact UH_mul _ _ _ hg (exp_mem_UH _ _ (lie_smul _ X hX t))
  · have : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by push_cast; rw [neg_smul]
    show NormedSpace.exp (-((t : ℂ) • X)) * g ∈ B.GV k r
    rw [this]
    exact UH_mul _ _ _ (exp_mem_UH _ _ (lie_smul _ X hX (-t))) hg

/- English proof (translation)
Break down `o with ⟨_ | _, X⟩` into its components or cases. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_ show HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Conclude with `HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g i l * NormedSpace.exp ((t : ℂ) • X) l j) fun l _ => (entry_hasDerivAt X l j).const_mul (g i l)`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_ show HasDerivAt (fun t : ℝ => (NormedSpace.exp (-((t : ℂ) • X)) * g) i j) ((-(X * g)) i j) 0` and prove the remaining obligations.

Establish `e : ∀ t : ℝ, -((t : ℂ) • X) = (t : ℂ) • (-X)` using `fun t => (smul_neg _ _).symm`. Simplify using `only [e, Matrix.mul_apply]`. Use `HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => NormedSpace.exp ((t : ℂ) • (-X)) i l * g l j) fun l _ => (entry_hasDerivAt (-X) i l).mul_const (g l j)` as an intermediate fact. Establish `hv : (-(X * g)) i j = ∑ l, (-X) i l * g l j`. Simplify using `[Matrix.mul_apply, Finset.sum_neg_distrib]`.

Rewrite using `[hv]`. Conclude with `this`.
-/
theorem curve_hasDerivAt (o : Bool × B.Mat k r) (g : B.Mat k r) :
    HasDerivAt (curve o g) (dir o g) 0 := by
  rcases o with ⟨_ | _, X⟩
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    show HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g i l * NormedSpace.exp ((t : ℂ) • X) l j)
      fun l _ => (entry_hasDerivAt X l j).const_mul (g i l)
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    show HasDerivAt (fun t : ℝ => (NormedSpace.exp (-((t : ℂ) • X)) * g) i j) ((-(X * g)) i j) 0
    have e : ∀ t : ℝ, -((t : ℂ) • X) = (t : ℂ) • (-X) := fun t => (smul_neg _ _).symm
    simp only [e, Matrix.mul_apply]
    have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => NormedSpace.exp ((t : ℂ) • (-X)) i l * g l j)
      fun l _ => (entry_hasDerivAt (-X) i l).mul_const (g l j)
    have hv : (-(X * g)) i j = ∑ l, (-X) i l * g l j := by
      simp [Matrix.mul_apply, Finset.sum_neg_distrib]
    rw [hv]
    exact this

/- English proof (translation)
Break down `o with ⟨_ | _, X⟩` into its components or cases. Set `L : B.Mat k r →ₗ[ℝ] B.Mat k r` to `{ toFun := fun g => g * X map_add' := fun a b => Matrix.add_mul a b X map_smul' := fun c a => Matrix.smul_mul c a X }`. Conclude with `(LinearMap.toContinuousLinearMap L).contDiff`. Set `L : B.Mat k r →ₗ[ℝ] B.Mat k r` to `{ toFun := fun g => -(X * g) map_add' := fun a b => by simp only [Matrix.mul_add, neg_add] map_smul' := fun c a => by simp only [Matrix.mul_smul, smul_neg, RingHom.id_apply] }`. Conclude with `(LinearMap.toContinuousLinearMap L).contDiff`.
-/
theorem dir_contDiff (o : Bool × B.Mat k r) : ContDiff ℝ ∞ (dir o) := by
  rcases o with ⟨_ | _, X⟩
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun g => g * X
        map_add' := fun a b => Matrix.add_mul a b X
        map_smul' := fun c a => Matrix.smul_mul c a X }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun g => -(X * g)
        map_add' := fun a b => by simp only [Matrix.mul_add, neg_add]
        map_smul' := fun c a => by simp only [Matrix.mul_smul, smul_neg, RingHom.id_apply] }
    exact (LinearMap.toContinuousLinearMap L).contDiff

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ f' g` using `(hf'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)`. Establish `hc` using `curve_hasDerivAt o g`. Establish `h1 : HasDerivAt (f' ∘ curve o g) (fderiv ℝ f' g (dir o g)) 0` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (curve_zero o g).symm`. Use `h1.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hcont : ContinuousAt (curve o g) 0` using `hc.continuousAt`.

Establish `hev : ∀ᶠ t in 𝓝 (0 : ℝ), curve o g t ∈ U` using `hcont.preimage_mem_nhds (by rw [curve_zero]; exact hU.mem_nhds hgU)`. Use `filter_upwards [hev] with t ht`. Conclude with `hagree _ ht (curve_mem o g t hX hg)`.
-/
theorem along (H : B.Mat k r → E) {U : Set (B.Mat k r)} {f' : B.Mat k r → E} (hU : IsOpen U)
    (hf' : ContDiffOn ℝ ∞ f' U) (hagree : ∀ g ∈ U, g ∈ B.GV k r → H g = f' g)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hgU : g ∈ U) (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t => H (curve o g t)) (fderiv ℝ f' g (dir o g)) 0 := by
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  have hc := curve_hasDerivAt o g
  have h1 : HasDerivAt (f' ∘ curve o g) (fderiv ℝ f' g (dir o g)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (curve_zero o g).symm
  refine h1.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (curve o g) 0 := hc.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), curve o g t ∈ U :=
    hcont.preimage_mem_nhds (by rw [curve_zero]; exact hU.mem_nhds hgU)
  filter_upwards [hev] with t ht
  exact hagree _ ht (curve_mem o g t hX hg)

/- English proof (translation)
Take `⟨U, f', hU, hgU, hf', hagree⟩` from `hH g hg`. Conclude with `⟨_, along H hU hf' hagree o hX g hgU hg⟩`.
-/
theorem exists_along (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    ∃ v, HasDerivAt (fun t => H (curve o g t)) v 0 := by
  obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hH g hg
  exact ⟨_, along H hU hf' hagree o hX g hgU hg⟩

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg₀U, hf', hagree⟩` from `hH g₀ hg₀`. Use `⟨U, fun g => fderiv ℝ f' g (dir o g), hU, hg₀U, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hf'.fderiv_of_isOpen hU (by simp)).clm_apply (dir_contDiff o).contDiffOn`. Introduce `g hgU hg`.

Rewrite using `[act_eq]`. Conclude with `(along H hU hf' hagree o hX g hgU hg).deriv`.
-/
theorem act_ck (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (act o H) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hagree⟩ := hH g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (dir o g), hU, hg₀U, ?_, ?_⟩
  · exact (hf'.fderiv_of_isOpen hU (by simp)).clm_apply (dir_contDiff o).contDiffOn
  · intro g hgU hg
    rw [act_eq]
    exact (along H hU hf' hagree o hX g hgU hg).deriv

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[act_eq]`. Establish `h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0)` using `((hQ.differentiable (by norm_num)) _).hasFDerivAt`. Establish `h2` using `h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)`. Rewrite `h2` using `[curve_zero]`.

Conclude with `h2.deriv`.
-/
theorem act_smooth (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) (o : Bool × B.Mat k r) :
    act o Q = fun g => fderiv ℝ Q g (dir o g) := by
  funext g
  rw [act_eq]
  have h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0) :=
    ((hQ.differentiable (by norm_num)) _).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)
  rw [curve_zero] at h2
  exact h2.deriv

/- English proof (translation)
Rewrite using `[act_smooth Q hQ o]`. Conclude with `(hQ.fderiv_right (by simp)).clm_apply (dir_contDiff o)`.
-/
theorem act_smooth_contDiff (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) (o : Bool × B.Mat k r) :
    ContDiff ℝ ∞ (act o Q) := by
  rw [act_smooth Q hQ o]
  exact (hQ.fderiv_right (by simp)).clm_apply (dir_contDiff o)

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, Q, isOpen_univ, Set.mem_univ _, hQ.contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem smooth_ck (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) : B.CkOn (⊤ : ℕ∞) (B.GV k r) Q :=
  fun _ _ => ⟨Set.univ, Q, isOpen_univ, Set.mem_univ _, hQ.contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hg₀U, hf', hagree⟩` from `hH g₀ hg₀`. Use `⟨U, fun g => Q g • f' g, hU, hg₀U, hQ.contDiffOn.smul hf', ?_⟩` and prove the remaining obligations. Introduce `g hgU hg`. Simplify using `only [hagree g hgU hg]`.
-/
theorem smul_ck (Q : B.Mat k r → ℂ) (hQ : ContDiff ℝ ∞ Q) (H : B.Mat k r → E)
    (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => Q g • H g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hagree⟩ := hH g₀ hg₀
  refine ⟨U, fun g => Q g • f' g, hU, hg₀U, hQ.contDiffOn.smul hf', ?_⟩
  intro g hgU hg
  simp only [hagree g hgU hg]

/- English proof (translation)
Rewrite using `[act_eq, act_eq]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `h _ (curve_mem o g t hX hg)`.
-/
theorem act_local (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (f₁ f₂ : B.Mat k r → E)
    (h : ∀ g ∈ B.GV k r, f₁ g = f₂ g) (g : B.Mat k r) (hg : g ∈ B.GV k r) : act o f₁ g = act o f₂ g := by
  rw [act_eq, act_eq]
  congr 1
  funext t
  exact h _ (curve_mem o g t hX hg)

/- English proof (translation)
Take `⟨v₁, hv₁⟩` from `exists_along f₁ h₁ o hX g hg`. Take `⟨v₂, hv₂⟩` from `exists_along f₂ h₂ o hX g hg`. Rewrite using `[act_eq, act_eq, act_eq, hv₁.deriv, hv₂.deriv]`. Conclude with `(hv₁.add hv₂).deriv`.
-/
theorem act_add (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (f₁ f₂ : B.Mat k r → E)
    (h₁ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁) (h₂ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    act o (fun x => f₁ x + f₂ x) g = act o f₁ g + act o f₂ g := by
  obtain ⟨v₁, hv₁⟩ := exists_along f₁ h₁ o hX g hg
  obtain ⟨v₂, hv₂⟩ := exists_along f₂ h₂ o hX g hg
  rw [act_eq, act_eq, act_eq, hv₁.deriv, hv₂.deriv]
  exact (hv₁.add hv₂).deriv

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_along H hH o hX g hg`. Establish `h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0)` using `((hQ.differentiable (by norm_num)) _).hasFDerivAt`. Establish `hQd` using `h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)`. Rewrite `hQd` using `[curve_zero]`. Rewrite using `[act_eq, act_eq, act_eq, hv.deriv, show deriv (fun t => Q (curve o g t)) 0 = fderiv ℝ Q g (dir o g) from hQd.deriv]`.

Rewrite using `[show deriv (fun t => Q (curve o g t) • H (curve o g t)) 0 = (Q ∘ curve o g) 0 • v + fderiv ℝ Q g (dir o g) • H (curve o g 0) from (hQd.smul hv).deriv]`. Simplify using `only [Function.comp_apply, curve_zero]`. Rewrite using `[add_comm]`.
-/
theorem act_leib (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (Q : B.Mat k r → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    act o (fun x => Q x • H x) g = act o Q g • H g + Q g • act o H g := by
  obtain ⟨v, hv⟩ := exists_along H hH o hX g hg
  have h1 : HasFDerivAt Q (fderiv ℝ Q (curve o g 0)) (curve o g 0) :=
    ((hQ.differentiable (by norm_num)) _).hasFDerivAt
  have hQd := h1.comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt o g)
  rw [curve_zero] at hQd
  rw [act_eq, act_eq, act_eq, hv.deriv,
    show deriv (fun t => Q (curve o g t)) 0 = fderiv ℝ Q g (dir o g) from hQd.deriv]
  rw [show deriv (fun t => Q (curve o g t) • H (curve o g t)) 0 =
      (Q ∘ curve o g) 0 • v + fderiv ℝ Q g (dir o g) • H (curve o g 0) from (hQd.smul hv).deriv]
  simp only [Function.comp_apply, curve_zero]
  rw [add_comm]

end sup

end CCRuleCW
