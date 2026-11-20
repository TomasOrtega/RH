import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

/- English proof (translation)
Establish `hzc` using `hz.1`. Establish `hpr : T.L.pr (z⁻¹ * g) = T.L.pr g`. Rewrite using `[map_mul, map_inv, hz.2, inv_one, one_mul]`. Establish `key : ∀ a b : X, a * (h * z) * b = z * (a * h * b)`. Introduce `a b`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmem : g ∈ DoubleCoset.doubleCoset (h * z) (T.K : Set X) T.K ↔ z⁻¹ * g ∈ DoubleCoset.doubleCoset h (T.K : Set X) T.K`. Simplify using `only [DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`.

Conclude with `⟨a, ha, b, hb, by rw [key]; group⟩`. Introduce and unpack `⟨a, ha, b, hb, he⟩`. Use `⟨a, ha, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← he]`. Use `group`.

Simplify using `only [TyLev.tf, dosetInd, hpr, Set.indicator_apply, hmem, Pi.one_apply]`.
-/
private theorem UpperTheory.Gal.W2.Seed.tf_mul_cen_apply {X M : Type} [Group X] [Group M] (T : TyLev X M)
    (h z : X) (hz : T.Cen z) (g : X) : T.tf (h * z) g = T.tf h (z⁻¹ * g) := by
  have hzc := hz.1
  have hpr : T.L.pr (z⁻¹ * g) = T.L.pr g := by
    rw [map_mul, map_inv, hz.2, inv_one, one_mul]
  have key : ∀ a b : X, a * (h * z) * b = z * (a * h * b) := by
    intro a b
    calc a * (h * z) * b = a * h * (z * b) := by group
      _ = a * h * (b * z) := by rw [hzc b]
      _ = (a * h * b) * z := by group
      _ = z * (a * h * b) := (hzc _).symm
  have hmem : g ∈ DoubleCoset.doubleCoset (h * z) (T.K : Set X) T.K ↔
      z⁻¹ * g ∈ DoubleCoset.doubleCoset h (T.K : Set X) T.K := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [key]; group⟩
    · rintro ⟨a, ha, b, hb, he⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [key, ← he]
      group
  simp only [TyLev.tf, dosetInd, hpr, Set.indicator_apply, hmem, Pi.one_apply]

/- English proof (translation)
Introduce `hAdm hCen hIdem X M _ _ T h z hh hz`. Establish `hzc : ∀ y : X, z⁻¹ * y = y * z⁻¹` using `fun y => (Commute.inv_left (hz.1 y : Commute z y)).eq`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `hty : T.IsTy (V` using `ℂ) (fun y : X => T.tf h (y⁻¹ * g)) := by`.

Introduce `k hk y`. Establish `e` using `((hAdm X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1`. Simplify using `only [mul_inv_rev, mul_assoc]`. Rewrite using `[e]`. Simplify using `only [map_inv, smul_eq_mul]`.

Use `congr 1`. Rewrite using `[← map_inv]`. Conclude with `congrArg (fun u => ((T.ψ u : ℂˣ) : ℂ)) (Subtype.ext (inv_inv _))`. Establish `e` using `hCen X M T z hz ℂ (fun y => T.tf h (y⁻¹ * g)) hty 1`. Simplify using `only [hAct, one_mul, smul_eq_mul] at e`.

Simplify using `only [conv]`. Rewrite using `[e, tf_mul_cen_apply T h z hz g]`. Use function extensionality and compare the values at `g`. Establish `e1 : conv T.K₀ (T.tf h) (T.tf z) g = conv T.K₀ (T.tf h) (T.tf 1) (z⁻¹ * g)`. Simplify using `only [conv]`.

Use `finsum_congr fun x => ?_` and prove the remaining obligations. Use `congr 1`. Establish `e` using `tf_mul_cen_apply T 1 z hz (x.out⁻¹ * g)`. Rewrite `e` using `[one_mul]`. Rewrite using `[e, ← mul_assoc, ← mul_assoc, hzc]`.

Rewrite using `[e1, (hIdem X M T h hh).2.1, tf_mul_cen_apply T h z hz g]`.
-/
theorem UpperTheory.Gal.W2.Seed.pTfMulCen :
    TfAdm → TfCen → TfIdem → TfMulCen := by
  intro hAdm hCen hIdem X M _ _ T h z hh hz
  have hzc : ∀ y : X, z⁻¹ * y = y * z⁻¹ := fun y => (Commute.inv_left (hz.1 y : Commute z y)).eq
  refine ⟨?_, ?_⟩
  · funext g
    have hty : T.IsTy (V := ℂ) (fun y : X => T.tf h (y⁻¹ * g)) := by
      intro k hk y
      have e := ((hAdm X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
      simp only [mul_inv_rev, mul_assoc]
      rw [e]
      simp only [map_inv, smul_eq_mul]
      congr 1
      rw [← map_inv]
      exact congrArg (fun u => ((T.ψ u : ℂˣ) : ℂ)) (Subtype.ext (inv_inv _))
    have e := hCen X M T z hz ℂ (fun y => T.tf h (y⁻¹ * g)) hty 1
    simp only [hAct, one_mul, smul_eq_mul] at e
    simp only [conv]
    rw [e, tf_mul_cen_apply T h z hz g]
  · funext g
    have e1 : conv T.K₀ (T.tf h) (T.tf z) g = conv T.K₀ (T.tf h) (T.tf 1) (z⁻¹ * g) := by
      simp only [conv]
      refine finsum_congr fun x => ?_
      congr 1
      have e := tf_mul_cen_apply T 1 z hz (x.out⁻¹ * g)
      rw [one_mul] at e
      rw [e, ← mul_assoc, ← mul_assoc, hzc]
    rw [e1, (hIdem X M T h hh).2.1, tf_mul_cen_apply T h z hz g]
