import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

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
Set `e₁ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ)` to `.ofFinrankEq (Module.finrank_fin_fun ℝ).symm`. Set `e₂` to `(e₁.arrowCongr (1 : V ≃L[ℝ] V)).trans (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ V)))`. Establish `e : f = fun y => e₂.symm (e₂ (f y))` using `funext fun y => (e₂.symm_apply_apply _).symm`. Rewrite using `[e]`. Conclude with `e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.2 fun i => h _)`.
-/
private theorem clm_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : X → V →L[ℝ] V} {x : X} (h : ∀ v, ContDiffAt ℝ ∞ (fun y => f y v) x) : ContDiffAt ℝ ∞ f x := by
  let e₁ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := .ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : V ≃L[ℝ] V)).trans (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ V)))
  have e : f = fun y => e₂.symm (e₂ (f y)) := funext fun y => (e₂.symm_apply_apply _).symm
  rw [e]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.2 fun i => h _)

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

/- English proof (translation)
Introduce `E _ _ a`. Take `⟨σ, hσ, hs⟩` from `locSec E a (hOne E a) hOne_mem_cone`. Use `set k := σ (hOne E a) with hk`. Establish `hk1 : sand k⁻¹ (hOne E a) = hOne E a`. Establish `h0 : sand k (hOne E a) = hOne E a` using `hs.self_of_nhds`.

Use `conv_lhs => rw [← h0]`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Establish `h1 : ∀ i j, ContDiffAt ℝ ∞ (fun p => (σ p * k⁻¹).val i j) (hOne E a)` using `fun i j => by`. Simplify using `only [Units.val_mul, Matrix.mul_apply]`.

Conclude with `ContDiffAt.sum fun l _ => (contDiffAt_pi.1 (contDiffAt_pi.1 hσ i) l).mul contDiffAt_const`. Establish `h2 : ContDiffAt ℝ ∞ (fun p => toL (σ p * k⁻¹).val) (hOne E a)` using `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h1 i j`. Establish `h3` using `inv_smooth (τ := fun p => σ p * k⁻¹) h2`. Use `⟨fun p => σ p * k⁻¹, mul_inv_cancel k, h2, contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h3 i j, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `clm_smooth fun v => sand_smooth h1 v`.

Conclude with `clm_smooth fun v => sand_smooth (σ := fun p => (σ p * k⁻¹)⁻¹) h3 v`. Use `filter_upwards [hs] with p hp`. Rewrite using `[map_mul, ContinuousLinearMap.mul_apply, hk1, hp]`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.secOne :
    SecOne := by
  intro E _ _ a
  obtain ⟨σ, hσ, hs⟩ := locSec E a (hOne E a) hOne_mem_cone
  set k := σ (hOne E a) with hk
  have hk1 : sand k⁻¹ (hOne E a) = hOne E a := by
    have h0 : sand k (hOne E a) = hOne E a := hs.self_of_nhds
    conv_lhs => rw [← h0]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun p => (σ p * k⁻¹).val i j) (hOne E a) := fun i j => by
    simp only [Units.val_mul, Matrix.mul_apply]
    exact ContDiffAt.sum fun l _ => (contDiffAt_pi.1 (contDiffAt_pi.1 hσ i) l).mul contDiffAt_const
  have h2 : ContDiffAt ℝ ∞ (fun p => toL (σ p * k⁻¹).val) (hOne E a) :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h1 i j
  have h3 := inv_smooth (τ := fun p => σ p * k⁻¹) h2
  refine ⟨fun p => σ p * k⁻¹, mul_inv_cancel k, h2,
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h3 i j, ?_, ?_, ?_⟩
  · exact clm_smooth fun v => sand_smooth h1 v
  · exact clm_smooth fun v => sand_smooth (σ := fun p => (σ p * k⁻¹)⁻¹) h3 v
  · filter_upwards [hs] with p hp
    rw [map_mul, ContinuousLinearMap.mul_apply, hk1, hp]
