import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TorusAction

open InvAlg

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Unfold `mulLat`. Simplify using `only [Submodule.mem_map, LinearMap.mulLeft_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩`.
-/
theorem mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

/- English proof (translation)
Establish `h : (t : B.A) * B.σ (t : B.A) = 1` using `ht`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Use `_ = _ := by rw [h, mul_one]`.
-/
theorem sigma_eq_inv (t : B.Aˣ) (ht : t ∈ B.T) : B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) := by
  have h : (t : B.A) * B.σ (t : B.A) = 1 := ht
  calc B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * B.σ (t : B.A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

/- English proof (translation)
Use `⟨hL.1.map _, ?_⟩` and prove the remaining obligations. Establish `hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) = (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A)`. Unfold `mulLat`. Rewrite using `[Submodule.map_coe]`. Both sides reduce to the same expression.

Rewrite using `[hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]`. Introduce `y`. Conclude with `⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩`.
-/
theorem isLat_mulLat (u : B.Aˣ) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    unfold mulLat; rw [Submodule.map_coe]; rfl
  rw [hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩

/- English proof (translation)
Introduce `t ht L hL`. Take `⟨hlat, hg, hdual⟩` from `hL`. Establish `hs` using `sigma_eq_inv B t ht`. Use `⟨isLat_mulLat B t L hlat, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Rewrite `hy`, the goal using `[mem_mulLat_unit]`. Use `hg _ hy` as an intermediate fact. Rewrite `this` using `[mul_left_comm]`. Then use the resulting hypothesis. Introduce `y`. Rewrite using `[mem_mulLat_unit, hdual]`.

Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Rewrite `hz` using `[mem_mulLat_unit]`. Use `h _ hz` as an intermediate fact. Establish `e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z`.

Establish `hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A)` using `by rw [← hs, B.σ_σ]`. Unfold `InvAlg.herm`. Rewrite using `[map_mul B.σ, hs']`. Use `congr 1`. Take the linear combination `(x * y * B.σ z) * Units.inv_mul t`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `h w hw`. Establish `hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L`. Rewrite using `[mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `hw`.

Use `h _ hz` as an intermediate fact. Establish `e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w)`. Unfold `InvAlg.herm`. Rewrite using `[map_mul B.σ, hs]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem torus_mem_X (K : UQ) (B : InvAlg K) (x : B.A) :
    ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  intro t ht L hL
  obtain ⟨hlat, hg, hdual⟩ := hL
  have hs := sigma_eq_inv B t ht
  refine ⟨isLat_mulLat B t L hlat, ?_, ?_⟩
  · intro y hy
    rw [mem_mulLat_unit] at hy ⊢
    have := hg _ hy
    rwa [mul_left_comm] at this
  · intro y
    rw [mem_mulLat_unit, hdual]
    constructor
    · intro h z hz
      rw [mem_mulLat_unit] at hz
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z := by
        have hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A) := by rw [← hs, B.σ_σ]
        unfold InvAlg.herm; rw [map_mul B.σ, hs']
        congr 1
        linear_combination (x * y * B.σ z) * Units.inv_mul t
      rwa [e] at this
    · intro h w hw
      have hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L := by
        rw [mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w) := by
        unfold InvAlg.herm; rw [map_mul B.σ, hs]; congr 1; ring
      rwa [e]

end GlobalTheory.UnitLemma.TorusAction
