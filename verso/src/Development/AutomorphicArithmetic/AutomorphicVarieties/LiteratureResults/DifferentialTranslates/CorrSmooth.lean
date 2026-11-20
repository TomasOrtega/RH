import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/- English proof (translation)
Take `⟨r, hr⟩` from `(HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)`. Establish `e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1`. Use function extensionality and compare the values at `fun y => (LinearMap.congr_fun hr (f y)).symm`. Rewrite using `[e]`. Conclude with `(LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h`.
-/
private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

/- English proof (translation)
Establish `hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x` using `(contDiff_det (E := E) (a := a)).contDiffAt.comp x h`. Establish `hu : IsUnit (τ x).val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit`. Establish `hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x`. Use `contDiffAt_ringInverse ℝ (n := ∞) hu.unit` as an intermediate fact. Rewrite `this` using `[hu.unit_spec]`.

Conclude with `this.comp x hd`. Establish `ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x`. Simplify using `only [Matrix.adjugate_apply]`. Use `(contDiff_det (E := E) (a := a)).contDiffAt.comp x (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_` and prove the remaining obligations. Use `contDiffAt_pi.2 fun k => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Establish `: (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1`. Use function extensionality and compare the values at `fun y => Matrix.updateRow_self`. Rewrite using `[this]`.

Conclude with `contDiffAt_const`. Establish `: (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k`. Use function extensionality and compare the values at `fun y => Matrix.updateRow_ne hk`. Rewrite using `[this]`. Conclude with `contDiffAt_pi.1 h k`.

Establish `e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j`. Use function extensionality and compare the values at `y`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hi.mul ha`.
-/
private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x := (contDiff_det (E := E) (a := a)).contDiffAt.comp x h
  have hu : IsUnit (τ x).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit
  have hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [hu.unit_spec] at this
    exact this.comp x hd
  have ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine (contDiff_det (E := E) (a := a)).contDiffAt.comp x
      (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_
    refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      have : (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1 :=
        funext fun y => Matrix.updateRow_self
      rw [this]; exact contDiffAt_const
    · have : (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k :=
        funext fun y => Matrix.updateRow_ne hk
      rw [this]; exact contDiffAt_pi.1 h k
  have e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j := by
    funext y
    rw [Matrix.coe_units_inv, Matrix.inv_def]; rfl
  rw [e]
  exact hi.mul ha

/- English proof (translation)
Use `sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)` and prove the remaining obligations. Establish `e : (fun y => (sand (σ y) v).1 i j) = fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l)`. Use function extensionality and compare the values at `y`. Express the relevant statement in the definitionally equal form `((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _`. Simplify using `[Matrix.mul_apply]`.

Rewrite using `[e]`. Use `ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_` and prove the remaining obligations. Conclude with `(starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)`.
-/
private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) v).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

/- English proof (translation)
Introduce `E _ _ _ a U Ξ q α w hc s p₀ hp₀`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective s`. Take `⟨τ, hτ, hs⟩` from `locSec E a p₀ hp₀`. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Use `set f : HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) := fun p => (w (x : GL (Fin a) (Af E) ⧸ U) p).compContinuousLinearMap ((2 : ℝ) • sand (τ p)) with hf`.

Establish `hfs : ContDiffAt ℝ ∞ f p₀`. Use `altSmooth _ _ _ q f p₀ fun Y => ?_` and prove the remaining obligations. Establish `h1 : ContDiffAt ℝ ∞ (fun p => Ξ.mat (τ p) *ᵥ ev (α fun i => hv.symm (Y i)) (infGL E a (τ p) * finGL E a x)) p₀`. Use `contDiffAt_pi.2 fun i => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`.

Use `ContDiffAt.sum fun j _ => ContDiffAt.mul ?_ ?_` and prove the remaining obligations. Use `(((matSmooth E a Ξ i j).1).contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet (τ p₀)))).comp p₀ hτ` as an intermediate fact. Simplify `this` using `only [Function.comp_def, extGL_val]`. Use `(contDiffAt_chart ((evFacts E a Ξ.d).2.1 (α fun i => hv.symm (Y i)) j) (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ` as an intermediate fact. Simplify `this` using `only [Function.comp_def, chart_val, infGL_comm]`.

Use `h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)` and prove the remaining obligations. Use `hc (τ p) x fun i => hv.symm (Y i)` as an intermediate fact. Simplify using `only [hp, LinearEquiv.apply_symm_apply] at this`. Conclude with `this`. Use `altSmooth _ _ _ q _ p₀ fun v => ?_` and prove the remaining obligations.

Establish `h2` using `applySmooth _ _ _ q f (fun i p => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)) p₀ hfs fun i => (sand_smooth (σ := fun p => (τ p)⁻¹) (inv_smooth hτ) (v i)).const_smul _`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w _ p v = w _ p _`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Establish `: sand (τ p) (sand (τ p)⁻¹ (v i)) = v i`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Simplify using `[this, smul_smul]`.
-/
theorem corrSmooth : CorrSmooth := by
  intro E _ _ _ a U Ξ q α w hc s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  set f : HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) := fun p =>
    (w (x : GL (Fin a) (Af E) ⧸ U) p).compContinuousLinearMap ((2 : ℝ) • sand (τ p)) with hf
  have hfs : ContDiffAt ℝ ∞ f p₀ := by
    refine altSmooth _ _ _ q f p₀ fun Y => ?_
    have h1 : ContDiffAt ℝ ∞ (fun p => Ξ.mat (τ p) *ᵥ
        ev (α fun i => hv.symm (Y i)) (infGL E a (τ p) * finGL E a x)) p₀ := by
      refine contDiffAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      refine ContDiffAt.sum fun j _ => ContDiffAt.mul ?_ ?_
      · have := (((matSmooth E a Ξ i j).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ p₀)))).comp p₀ hτ
        simpa only [Function.comp_def, extGL_val] using this
      · have := (contDiffAt_chart ((evFacts E a Ξ.d).2.1 (α fun i => hv.symm (Y i)) j) (finGL E a x)
          (val_mem_invSet (τ p₀))).comp p₀ hτ
        simpa only [Function.comp_def, chart_val, infGL_comm] using this
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hc (τ p) x fun i => hv.symm (Y i)
    simp only [hp, LinearEquiv.apply_symm_apply] at this
    exact this
  refine altSmooth _ _ _ q _ p₀ fun v => ?_
  have h2 := applySmooth _ _ _ q f (fun i p => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)) p₀ hfs
    fun i => (sand_smooth (σ := fun p => (τ p)⁻¹) (inv_smooth hτ) (v i)).const_smul _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  change w _ p v = w _ p _
  congr 1
  funext i
  have : sand (τ p) (sand (τ p)⁻¹ (v i)) = v i := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  simp [this, smul_smul]

end UpperTheory.V.Lit.Dr
