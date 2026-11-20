import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.SmoReg

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem Rt_mul_apply (g h : GA E a) (φ : XB E a) : Rt E a (g * h) φ = Rt E a g (Rt E a h φ) := by
  rw [map_mul]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 0, zero_le_one, fun g x => by have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _ simp [this]⟩`.
-/
theorem polyBd_repI [IsTotallyComplex E] : PolyBd (repI E a) :=
  ⟨1, 0, zero_le_one, fun g x => by
    have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _
    simp [this]⟩

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, k = c g` from `⟨_, rfl⟩`. Establish `hg1 : c ((f k)⁻¹ * g) = 1` using `by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]`. Establish `hcont : Continuous fun u : H => k⁻¹ * u * k` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1)`. Use `hcont.tendsto 1` as an intermediate fact.

Simplify using `using this`. Use `filter_upwards [hat hx] with u hu`. Establish `key : f u * g = g * f (k⁻¹ * u * k)`. Establish `h` using `hcomm _ hg1 (k⁻¹ * u * k)`. Establish `e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k` using `by simp only [map_mul, map_inv]`.

Rewrite `h`, the goal using `[e]`. Establish `h2` using `congrArg (f k * ·) h`. Simplify `h2.symm` using `only [mul_assoc, mul_inv_cancel_left]`. Establish `hu' : R (f (k⁻¹ * u * k)) x = x` using `hu`. Express the relevant statement in the definitionally equal form `R (f u) (R g x) = R g x`.

Rewrite using `[← hR, key, hR, hu']`.
-/
theorem conj_stab {G H X : Type} [Group G] [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : H →* G) (c : G →* H) (R : G → X → X) (hR : ∀ g h x, R (g * h) x = R g (R h x))
    (hf : ∀ u, c (f u) = u) (hcomm : ∀ g, c g = 1 → ∀ u, g * f u = f u * g)
    (g : G) (x : X) (hx : {u : H | R (f u) x = x} ∈ 𝓝 (1 : H)) :
    {u : H | R (f u) (R g x) = R g x} ∈ 𝓝 (1 : H) := by
  obtain ⟨k, hk⟩ : ∃ k, k = c g := ⟨_, rfl⟩
  have hg1 : c ((f k)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]
  have hcont : Continuous fun u : H => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    simpa using this
  filter_upwards [hat hx] with u hu
  have key : f u * g = g * f (k⁻¹ * u * k) := by
    have h := hcomm _ hg1 (k⁻¹ * u * k)
    have e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k := by simp only [map_mul, map_inv]
    rw [e] at h ⊢
    have h2 := congrArg (f k * ·) h
    simpa only [mul_assoc, mul_inv_cancel_left] using h2.symm
  have hu' : R (f (k⁻¹ * u * k)) x = x := hu
  change R (f u) (R g x) = R g x
  rw [← hR, key, hR, hu']

/- English proof (translation)
Introduce `w hw`. Establish `hx` using `hφ w hw`. Simplify using `only [repW_apply] at hx ⊢`. Conclude with `conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx`.
-/
theorem lev_Rt [IsTotallyComplex E] (hfl : ∀ (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)),
      cLoc w (fl a w u : GA E a) = u)
    (hcomm : ∀ (w : Pl E) (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g)
    (S : Finset (Pl E)) (g : GA E a) (φ : XB E a) (hφ : Lev S φ) : Lev S (Rt E a g φ) := by
  intro w hw
  have hx := hφ w hw
  simp only [repW_apply] at hx ⊢
  exact conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx

/- English proof (translation)
Introduce `hS2 hG0 E _ _ _ a S`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩` from `hG0 E a`. Take `⟨-, -, -, hgrp, hT, -⟩` from `hS2 _ a (XB E a) (repI E a) polyBd_repI`. Use `⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g φ hφ set y := cInf g with hy set gf : GA E a := (infGL E a y)⁻¹ * g with hgf`.

Establish `hgf1 : cInf gf = 1`. Rewrite using `[hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]`. Establish `hg : g = infGL E a y * gf` using `by rw [hgf, mul_inv_cancel_left]`. Establish `hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a), Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x)`. Introduce `z x`.

Express the relevant statement in the definitionally equal form `Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)`. Rewrite using `[← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]`. Use `hgrp y _ (hT (Rt E a gf) hc φ hφ)` as an intermediate fact. Establish `e : Rt E a g φ = repI E a y (Rt E a gf φ)`. Express the relevant statement in the definitionally equal form `Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)`.

Rewrite using `[← Rt_mul_apply, ← hg]`. Rewrite using `[e]`. Conclude with `this`. Introduce `c φ hφ w hw filter_upwards [hφ w hw] with u hu`. Establish `hu' : repW a w u φ = φ` using `hu`.

Express the relevant statement in the definitionally equal form `repW a w u (c • φ) = c • φ`. Rewrite using `[map_smul, hu']`. Introduce `φ φ' hφ hφ' w hw filter_upwards [hφ w hw, hφ' w hw] with u hu hu'`. Establish `e : repW a w u φ = φ` using `hu`. Establish `e' : repW a w u φ' = φ'` using `hu'`.

Express the relevant statement in the definitionally equal form `repW a w u (φ + φ') = φ + φ'`. Rewrite using `[map_add, e, e']`. Introduce `w hw filter_upwards with u`. Express the relevant statement in the definitionally equal form `repW a w u 0 = 0`. Rewrite using `[map_zero]`.
-/
theorem g5b : S2 → G0 → G5b := by
  intro hS2 hG0 E _ _ _ a S
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hG0 E a
  obtain ⟨-, -, -, hgrp, hT, -⟩ := hS2 _ a (XB E a) (repI E a) polyBd_repI
  refine ⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩
  · intro g φ hφ
    set y := cInf g with hy
    set gf : GA E a := (infGL E a y)⁻¹ * g with hgf
    have hgf1 : cInf gf = 1 := by
      rw [hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]
    have hg : g = infGL E a y * gf := by rw [hgf, mul_inv_cancel_left]
    have hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a),
        Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x) := by
      intro z x
      change Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)
      rw [← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]
    have := hgrp y _ (hT (Rt E a gf) hc φ hφ)
    have e : Rt E a g φ = repI E a y (Rt E a gf φ) := by
      change Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)
      rw [← Rt_mul_apply, ← hg]
    rw [e]
    exact this
  · intro c φ hφ w hw
    filter_upwards [hφ w hw] with u hu
    have hu' : repW a w u φ = φ := hu
    change repW a w u (c • φ) = c • φ
    rw [map_smul, hu']
  · intro φ φ' hφ hφ' w hw
    filter_upwards [hφ w hw, hφ' w hw] with u hu hu'
    have e : repW a w u φ = φ := hu
    have e' : repW a w u φ' = φ' := hu'
    change repW a w u (φ + φ') = φ + φ'
    rw [map_add, e, e']
  · intro w hw
    filter_upwards with u
    change repW a w u 0 = 0
    rw [map_zero]

end GlobalTheory.CompanionTheory.SmoReg

end
