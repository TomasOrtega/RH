import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.HermitianForms.Imports

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.Sep

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Use `congr 1`. Conclude with `Finset.sum_comm`.
-/
theorem sum_swap (X P Q : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, X a b * (P a b - Q b a) = ∑ a, ∑ b, (X a b * P a b - X b a * Q a b) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/- English proof (translation)
Establish `hs : ∀ (a b : Fin n) (z : ℂ), Matrix.single a b z = z.re • Matrix.single a b (1 : ℂ) + z.im • Matrix.single a b Complex.I`. Introduce `a b z`. Use extensionality with `i j`. Distinguish the cases in `h : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `h`.

Simplify using `[Complex.ext_iff]`. Establish `: ∀ w : ℂ, Matrix.single a b w i j = 0` using `fun w => by`. Rewrite using `[Matrix.single_apply_of_ne]`. The claim follows by propositional logic. Simplify using `[this]`.

Establish `hX' : ∀ a b, X b a = -conj (X a b)`. Introduce `a b`. Use `congrFun (congrFun hX a) b` as an intermediate fact. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this`. Establish `h2` using `congrArg (starRingEnd ℂ) this`.

Simplify using `using h2`. Establish `h1 : L X = ∑ a, ∑ b, (((X a b).re : ℂ) * L (Matrix.single a b 1) + ((X a b).im : ℂ) * L (Matrix.single a b Complex.I))` using `by conv_lhs => rw [Matrix.matrix_eq_sum_single X]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hs a b (X a b), map_add, map_smul, map_smul]`.

Simplify using `[Complex.real_smul]`. Rewrite using `[h1]`. Use `Eq.trans ?_ (sum_swap (fun a b => X a b) (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I))) (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) + Complex.I * L (Matrix.single a b Complex.I)))).symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[hX' a b]`. Establish `hc : conj (X a b) = ((X a b).re : ℂ) - ((X a b).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hz : ((X a b).re : ℂ) + ((X a b).im : ℂ) * Complex.I = X a b` using `Complex.re_add_im _`. Establish `key : ∀ x y p q : ℂ, x * p + y * q = (x + y * Complex.I) * ((1 / 2 : ℂ) * (p - Complex.I * q)) - (-(x - y * Complex.I)) * ((1 / 2 : ℂ) * (p + Complex.I * q))`.

Introduce `x y p q`. Take the linear combination `(y * q) * Complex.I_sq`. Use `key (X a b).re (X a b).im (L (Matrix.single a b 1)) (L (Matrix.single a b Complex.I))` as an intermediate fact. Rewrite `this` using `[hz, ← hc]`. Conclude with `this`.
-/
theorem real_linear_skew (L : Mat n →ₗ[ℝ] ℂ) (X : Mat n) (hX : Xᴴ = -X) :
    L X = ∑ a, ∑ b, X a b * ((1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I))
      - (1 / 2 : ℂ) * (L (Matrix.single b a 1) + Complex.I * L (Matrix.single b a Complex.I))) := by
  have hs : ∀ (a b : Fin n) (z : ℂ), Matrix.single a b z =
      z.re • Matrix.single a b (1 : ℂ) + z.im • Matrix.single a b Complex.I := by
    intro a b z
    ext i j
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [Complex.ext_iff]
    · have : ∀ w : ℂ, Matrix.single a b w i j = 0 := fun w => by
        rw [Matrix.single_apply_of_ne]
        tauto
      simp [this]
  have hX' : ∀ a b, X b a = -conj (X a b) := by
    intro a b
    have := congrFun (congrFun hX a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2
  have h1 : L X = ∑ a, ∑ b, (((X a b).re : ℂ) * L (Matrix.single a b 1) + ((X a b).im : ℂ) * L (Matrix.single a b Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs a b (X a b), map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  rw [h1]
  refine Eq.trans ?_ (sum_swap (fun a b => X a b)
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I)))
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) + Complex.I * L (Matrix.single a b Complex.I)))).symm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [hX' a b]
  have hc : conj (X a b) = ((X a b).re : ℂ) - ((X a b).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ((X a b).re : ℂ) + ((X a b).im : ℂ) * Complex.I = X a b := Complex.re_add_im _
  have key : ∀ x y p q : ℂ, x * p + y * q = (x + y * Complex.I) * ((1 / 2 : ℂ) * (p - Complex.I * q))
      - (-(x - y * Complex.I)) * ((1 / 2 : ℂ) * (p + Complex.I * q)) := by
    intro x y p q
    linear_combination (y * q) * Complex.I_sq
  have := key (X a b).re (X a b).im (L (Matrix.single a b 1)) (L (Matrix.single a b Complex.I))
  rw [hz, ← hc] at this
  exact this

/- English proof (translation)
Establish `e : (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (e1 GlobalTheory.CompanionTheory.ModelS.DR a b h).1 g - (f1 GlobalTheory.CompanionTheory.ModelS.DR b a h).1 g`. Simplify using `[GlobalTheory.CompanionTheory.ModelS.Kf, e2, sub_eq_add_neg]`. Rewrite using `[e, GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply b a h hg]`. Simplify using `[Eu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Kf_apply (a b : Fin n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (1 / 2 : ℂ) * (Rd (Matrix.single a b 1) h.1 g - Complex.I * Rd (Matrix.single a b Complex.I) h.1 g)
      - (1 / 2 : ℂ) * (Rd (Matrix.single b a 1) h.1 g + Complex.I * Rd (Matrix.single b a Complex.I) h.1 g) := by
  have e : (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (e1 GlobalTheory.CompanionTheory.ModelS.DR a b h).1 g - (f1 GlobalTheory.CompanionTheory.ModelS.DR b a h).1 g := by
    simp [GlobalTheory.CompanionTheory.ModelS.Kf, e2, sub_eq_add_neg]
  rw [e, GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply b a h hg]
  simp [Eu]
  ring

def AX (X : Mat n) : Module.End ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n) := ∑ a, ∑ b, X a b • GlobalTheory.CompanionTheory.ModelS.Kf a b

/- English proof (translation)
Set `L : Mat n →ₗ[ℝ] ℂ` to `((fderiv ℝ w.1 g).comp (GlobalTheory.CompanionTheory.RCalc.mulL g)).toLinearMap`. Establish `hL : ∀ v, L v = Rd v w.1 g` using `fun _ => rfl`. Establish `e : (AX X w).1 g = ∑ a, ∑ b, X a b * (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g`. Simplify using `[AX, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Rewrite using `[e, ← hL X, real_linear_skew L X hX]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Kf_apply a b w hg]`. Both sides reduce to the same expression.
-/
theorem AX_apply (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (AX X w).1 g = Rd X w.1 g := by
  let L : Mat n →ₗ[ℝ] ℂ := ((fderiv ℝ w.1 g).comp (GlobalTheory.CompanionTheory.RCalc.mulL g)).toLinearMap
  have hL : ∀ v, L v = Rd v w.1 g := fun _ => rfl
  have e : (AX X w).1 g = ∑ a, ∑ b, X a b * (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g := by
    simp [AX, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  rw [e, ← hL X, real_linear_skew L X hX]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Kf_apply a b w hg]
  rfl

/- English proof (translation)
Simplify using `only [AX, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b w hw)`.
-/
theorem AX_mem (X : Mat n) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n))
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) {w : GlobalTheory.CompanionTheory.ModelS.SmF n} (hw : w ∈ S) :
    AX X w ∈ S := by
  simp only [AX, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b w hw)

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X t`. Set `L : Mat n →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)`. Use `L.hasFDerivAt.comp_hasDerivAt t h` as an intermediate fact. Simplify using `only [Complex.coe_smul] at this ⊢`. Conclude with `this`.
-/
theorem exp_entry (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) ((NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt t h
  simp only [Complex.coe_smul] at this ⊢
  exact this

/- English proof (translation)
Establish `: HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ)) (fun i j => (NormedSpace.exp ((t : ℂ) • X) * X) i j) t`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Rewrite using `[hasDerivAt_pi]`. Introduce `j`.

Apply the tactic sequence `exact exp_entry X t i j`. Conclude with `this`.
-/
theorem exp_deriv (X : Mat n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X t i j
  exact this

/- English proof (translation)
Establish `h : IsUnit (NormedSpace.exp ((t : ℂ) • X))` using `(GlobalTheory.CompanionTheory.GLK.expG X t).isUnit`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero`.
-/
theorem exp_mem (X : Mat n) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GLs n := by
  have h : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := (GlobalTheory.CompanionTheory.GLK.expG X t).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero

/- English proof (translation)
Establish `hg` using `exp_mem X t`. Establish `hd` using `(GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth w.2.1 hg).hasFDerivAt`. Use `hd.comp_hasDerivAt t (exp_deriv X t)` as an intermediate fact. Rewrite using `[AX_apply X hX w hg]`. Conclude with `this`.
-/
theorem curve_deriv (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => w.1 (NormedSpace.exp ((t : ℂ) • X))) ((AX X w).1 (NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg := exp_mem X t
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth w.2.1 hg).hasFDerivAt
  have := hd.comp_hasDerivAt t (exp_deriv X t)
  rw [AX_apply X hX w hg]
  exact this

/- English proof (translation)
Use `ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0) (f := f) (g := fun _ => 0) (fun _ => B.lipschitz.lipschitzOnWith) (fun t => ⟨h t, trivial⟩) (fun t => ⟨by simpa using hasDerivAt_const t (0 : E), trivial⟩) h0` as an intermediate fact. Conclude with `congrFun this t`.
-/
theorem ode_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E) (f : ℝ → E)
    (h : ∀ t, HasDerivAt f (B (f t)) t) (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  have := ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
    (f := f) (g := fun _ => 0)
    (fun _ => B.lipschitz.lipschitzOnWith)
    (fun t => ⟨h t, trivial⟩) (fun t => ⟨by simpa using hasDerivAt_const t (0 : E), trivial⟩) h0
  exact congrFun this t

/- English proof (translation)
Set `bs` to `Module.finBasis ℂ S`. Set `C : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ` to `fun i j => bs.repr ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ j`. Establish `hexp : ∀ (u : S) (g : Mat n), u.1.1 g = ∑ j, bs.repr u j * (bs j).1.1 g`. Introduce `u g`. Establish `h` using `congrArg (fun v : S => v.1.1 g) (bs.sum_repr u)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Conclude with `h.symm`. Set `f : ℝ → Fin (Module.finrank ℂ S) → ℂ` to `fun t i => (bs i).1.1 (NormedSpace.exp ((t : ℂ) • X))`. Set `B : (Fin (Module.finrank ℂ S) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ S) → ℂ)` to `(LinearMap.toContinuousLinearMap (Matrix.toLin' C)).restrictScalars ℝ`. Establish `hd : ∀ t, HasDerivAt f (B (f t)) t`.

Introduce `t`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Establish `hc` using `curve_deriv X hX (bs i).1 t`. Establish `e : (AX X (bs i).1).1 (NormedSpace.exp ((t : ℂ) • X)) = B (f t) i`.

Use `hexp ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ (NormedSpace.exp ((t : ℂ) • X))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `show _ = (C.mulVec (f t)) i`. Both sides reduce to the same expression. Rewrite using `[← e]`.

Conclude with `hc`. Establish `h0 : f 0 = 0`. Use function extensionality and compare the values at `i`. Simplify `h1 _ (bs i).2` using `[f]`. Establish `hz` using `ode_zero B f hd h0 t`.

Rewrite using `[hexp ⟨w, hw⟩]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `: (bs j).1.1 (NormedSpace.exp ((t : ℂ) • X)) = 0` using `congrFun hz j`. Rewrite using `[this, mul_zero]`.
-/
theorem vanish_curve (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)) (fd : FiniteDimensional ℂ S)
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) (h1 : ∀ w ∈ S, w.1 1 = 0)
    (X : Mat n) (hX : Xᴴ = -X) (t : ℝ) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (hw : w ∈ S) :
    w.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := by
  classical
  let bs := Module.finBasis ℂ S
  let C : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    fun i j => bs.repr ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ j
  have hexp : ∀ (u : S) (g : Mat n), u.1.1 g = ∑ j, bs.repr u j * (bs j).1.1 g := by
    intro u g
    have h := congrArg (fun v : S => v.1.1 g) (bs.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  let f : ℝ → Fin (Module.finrank ℂ S) → ℂ := fun t i => (bs i).1.1 (NormedSpace.exp ((t : ℂ) • X))
  let B : (Fin (Module.finrank ℂ S) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ S) → ℂ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).restrictScalars ℝ
  have hd : ∀ t, HasDerivAt f (B (f t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have hc := curve_deriv X hX (bs i).1 t
    have e : (AX X (bs i).1).1 (NormedSpace.exp ((t : ℂ) • X)) = B (f t) i := by
      have := hexp ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ (NormedSpace.exp ((t : ℂ) • X))
      refine this.trans ?_
      show _ = (C.mulVec (f t)) i
      rfl
    rw [← e]
    exact hc
  have h0 : f 0 = 0 := by
    funext i
    simpa [f] using h1 _ (bs i).2
  have hz := ode_zero B f hd h0 t
  rw [hexp ⟨w, hw⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (bs j).1.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := congrFun hz j
  rw [this, mul_zero]

/- English proof (translation)
Introduce `n S fd hS h1 w hw k`. Take `⟨X, hX, hk⟩` from `GlobalTheory.CompanionTheory.UnitaryLog.main n k`. Use `vanish_curve S fd hS h1 X hX 1 w hw` as an intermediate fact. Simplify using `only [Complex.ofReal_one, one_smul] at this`. Rewrite using `[hk]`.

Conclude with `this`.
-/
theorem main : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S →
    (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
    ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  intro n S fd hS h1 w hw k
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryLog.main n k
  have := vanish_curve S fd hS h1 X hX 1 w hw
  simp only [Complex.ofReal_one, one_smul] at this
  rw [hk]
  exact this

end GlobalTheory.CompanionTheory.ModelS.Sep
