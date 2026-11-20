import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameterStatement
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using contDiff_const`. Consider the case `succ k ih`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Use `ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ ℝ 0)) ?_` and prove the remaining obligations.

Establish `h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ` using `contDiff_pi.2 fun a => contDiff_apply ℝ ℝ a.succ`. Conclude with `(ih fun a => I a.succ).comp h`.
-/
theorem contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ ℝ 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ ℝ a.succ
    exact (ih fun a => I a.succ).comp h

/- English proof (translation)
Introduce `G _ M _ ι c hc hM hcont`. Set `V` to `Fin (Module.finrank ℂ M) → ℂ`. Set `Φ : M ≃L[ℂ] V` to `(Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv`. Set `ρ : ι → ℝ → (M →ₗ[ℂ] M)` to `fun i t => { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `R : ι → ℝ → (V →L[ℂ] V)` to `fun i t => LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)`.

Establish `hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v))` using `fun _ _ _ => rfl`. Set `ev : G → (V →L[ℂ] ℂ)` to `fun g => LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)`. Establish `hev : ∀ g v, ev g v = (Φ.symm v).1 g` using `fun _ _ => rfl`. Establish `hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v`. Introduce `g i t v`.

Rewrite using `[hev, hRapp, Φ.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w`. Introduce `v w h`. Apply `Φ.symm.injective` to reduce the goal to its premises.

Conclude with `Subtype.ext (funext h)`. Establish `hc0 : ∀ i, c i 0 = 1`. Introduce `i`. Use `hc i 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_mul.1 this`. Establish `hR : ∀ i, ContDiff ℝ ∞ (R i)`. Introduce `i`. Use `GlobalTheory.T.contDiff_of_continuous_oneParameter_hom _ (R i) ?_ ?_ ?_` and prove the remaining obligations. Use `continuous_clm_apply.2 fun v => ?_` and prove the remaining obligations.

Simplify using `only [hRapp]`. Use `Φ.continuous.comp ?_` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _`. Use `ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[hkey, hc0, mul_one]`.

Both sides reduce to the same expression. Introduce `s t`. Use `ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]`. Establish `hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩)`.

Introduce `f hf g`. Rewrite using `[hev, Φ.symm_apply_apply]`. Use `⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩` and prove the remaining obligations. Establish `hd : HasDerivAt (R i) (deriv (R i) 0) 0` using `((hR i).differentiable (by simp) 0).hasDerivAt`. Establish `: (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1`.

Use function extensionality and compare the values at `g`. Rewrite using `[← hev]`. Establish `h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩))`. Use function extensionality and compare the values at `t`. Rewrite using `[hkey, ← hf]`.

Rewrite using `[h1]`. Set `L : (V →L[ℂ] V) →L[ℂ] ℂ` to `(ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))`. Conclude with `((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv`. Rewrite using `[this]`. Conclude with `Subtype.property _`.

Establish `hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V), ev g ((List.ofFn fun a => R (I a) (t a)).prod v) = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro I t g v`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `I t g v`. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Rewrite using `[ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ), mul_assoc]`. Establish `h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod)) = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩))`.

Use function extensionality and compare the values at `t`. Rewrite using `[hprod, ← hf]`. Rewrite using `[h1]`. Set `L : (V →L[ℂ] V) →L[ℂ] ℂ` to `(ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))`. Conclude with `(L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)`.
-/
theorem smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  intro G _ M _ ι c hc hM hcont
  let V := Fin (Module.finrank ℂ M) → ℂ
  let Φ : M ≃L[ℂ] V := (Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv
  let ρ : ι → ℝ → (M →ₗ[ℂ] M) := fun i t =>
    { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R : ι → ℝ → (V →L[ℂ] V) := fun i t =>
    LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v)) := fun _ _ _ => rfl
  let ev : G → (V →L[ℂ] ℂ) := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hev : ∀ g v, ev g v = (Φ.symm v).1 g := fun _ _ => rfl
  have hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v := by
    intro g i t v
    rw [hev, hRapp, Φ.symm_apply_apply]
    rfl
  have hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w := by
    intro v w h
    apply Φ.symm.injective
    exact Subtype.ext (funext h)
  have hc0 : ∀ i, c i 0 = 1 := by
    intro i
    have := hc i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hR : ∀ i, ContDiff ℝ ∞ (R i) := by
    intro i
    refine GlobalTheory.T.contDiff_of_continuous_oneParameter_hom _ (R i) ?_ ?_ ?_
    · refine continuous_clm_apply.2 fun v => ?_
      simp only [hRapp]
      refine Φ.continuous.comp ?_
      exact Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _
    · refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [hkey, hc0, mul_one]; rfl
    · intro s t
      refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]
  have hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩) := by
    intro f hf g
    rw [hev, Φ.symm_apply_apply]
  refine ⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩
  · have hd : HasDerivAt (R i) (deriv (R i) 0) 0 :=
      ((hR i).differentiable (by simp) 0).hasDerivAt
    have : (fun g => deriv (fun t : ℝ => f (g * c i t)) 0)
        = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1 := by
      funext g
      rw [← hev]
      have h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩)) := by
        funext t
        rw [hkey, ← hf]
      rw [h1]
      let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
      exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv
    rw [this]
    exact Subtype.property _
  · have hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V),
        ev g ((List.ofFn fun a => R (I a) (t a)).prod v)
          = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v := by
      intro k
      induction k with
      | zero => intro I t g v; simp
      | succ k ih =>
        intro I t g v
        simp only [List.ofFn_succ, List.prod_cons]
        rw [ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ),
          mul_assoc]
    have h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod))
        = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩)) := by
      funext t
      rw [hprod, ← hf]
    rw [h1]
    let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
    exact (L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)

end GlobalTheory
