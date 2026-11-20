import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Group

variable {k r : ℕ}

/- English proof (translation)
Simplify using `[UWset, UH]`.
-/
theorem sv_one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

/- English proof (translation)
Assemble the required witnesses or components as `⟨B5.exp_mem hX.1 t, fun a => ⟨Qx2.exp_fix (hX.2.2 a).1 t, Qx2.exp_fix (hX.2.2 a).2 t⟩, Qx2.exp_fix hX.2.1 t⟩`.
-/
theorem sv_exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : inLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z :=
  ⟨B5.exp_mem hX.1 t, fun a => ⟨Qx2.exp_fix (hX.2.2 a).1 t, Qx2.exp_fix (hX.2.2 a).2 t⟩, Qx2.exp_fix hX.2.1 t⟩

/- English proof (translation)
Simplify using `only [UWset, Glev, UH, Set.mem_setOf_eq] at hh hg ⊢`. Take `⟨hh1, hh2, -⟩` from `hh`. Take `⟨hg1, hg2⟩` from `hg`. Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hh1, hg1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hg2 a ha).1, (hh2 a).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hg2 a ha).2, (hh2 a).2]`.
-/
theorem sv_uw_glev {z : Fin (2 * r + k + 1) → ℂ} {h g : Mx k r} (hh : h ∈ UWset k r z)
    (hg : g ∈ Glev k r (Fin.last r)) : h * g ∈ Glev k r (Fin.last r) := by
  simp only [UWset, Glev, UH, Set.mem_setOf_eq] at hh hg ⊢
  obtain ⟨hh1, hh2, -⟩ := hh
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul]
    calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hh1, hg1]
  · rw [← Matrix.mulVec_mulVec, (hg2 a ha).1, (hh2 a).1]
  · rw [← Matrix.mulVec_mulVec, (hg2 a ha).2, (hh2 a).2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(nSubgroup k r).1, WeylGroupFacts.uh_one, fun _ _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩`.
-/
theorem sv_one_nlev (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i :=
  ⟨(nSubgroup k r).1, WeylGroupFacts.uh_one, fun _ _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩

/- English proof (translation)
Use `show ∃ h' ∈ UWset k r z, ∃ m ∈ Nlev k r i, h = h' * m`. Conclude with `⟨h, hh, 1, sv_one_nlev i, (mul_one h).symm⟩`.
-/
theorem sv_uw_slev {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (i : Fin (r + 1)) :
    h ∈ Slev k r z i := by
  show ∃ h' ∈ UWset k r z, ∃ m ∈ Nlev k r i, h = h' * m
  exact ⟨h, hh, 1, sv_one_nlev i, (mul_one h).symm⟩

end Group

section SmoothJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

/- English proof (translation)
Introduce `h hh X hX`. Establish `h1' : (1 : Mx k r) ∈ UWset k r z'` using `sv_one_uw z'`. Establish `he : ∀ t : ℝ, π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v) = J (h * NormedSpace.exp ((t : ℂ) • X) * g) v`. Introduce `t`. Establish `hm` using `hJ.2.2.2 g hg _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) 1 h1'`.

Rewrite `hm` using `[Matrix.mul_one]`. Rewrite using `[hm]`. Simplify using `[hπ'1]`. Establish `hfun : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v)) = fun t : ℝ => J (h * NormedSpace.exp ((t : ℂ) • X) * g) v` using `funext he`. Rewrite using `[hfun]`.

Establish `hhg : h * g ∈ Glev k r (Fin.last r) ∩ D`. Use `⟨sv_uw_glev hh hg.1, ?_⟩` and prove the remaining obligations. Use `hD.2 g hg h (sv_uw_slev hh _) 1 (sv_uw_slev h1' _)` as an intermediate fact. Simplify using `using this`. Take `⟨U, F, hU, hgU, hF, hFe⟩` from `hJ.1 (h * g) hhg`.

Establish `hd : DifferentiableAt ℝ F (h * g)` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Establish `hc : HasDerivAt (fun t : ℝ => h * NormedSpace.exp ((t : ℂ) • X) * g) (mulRightRealCLM g (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X)) 0` using `(mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (B5.curve_hasDerivAt h X 0)`. Establish `hc0 : h * g = h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g`. Simplify using `[NormedSpace.exp_zero]`. Establish `hFc : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g)) 0` using `(hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).differentiableAt`.

Establish `hFv : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g) v) 0` using `((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hFc`. Use `hFv.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, h * NormedSpace.exp ((t : ℂ) • X) * g ∈ U` using `hc.continuousAt.preimage_mem_nhds (by rw [← hc0]; exact hU.mem_nhds hgU)`. Use `filter_upwards [hmem] with t ht`. Rewrite using `[hFe _ ht (sv_uw_glev (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) hg.1)]`.
-/
theorem J_smoothVec (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D) (hπ'1 : π' 1 = 1)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (v : Wq) : J g v ∈ SmVec k r z π := by
  intro h hh X hX
  have h1' : (1 : Mx k r) ∈ UWset k r z' := sv_one_uw z'
  have he : ∀ t : ℝ, π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v) =
      J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := by
    intro t
    have hm := hJ.2.2.2 g hg _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) 1 h1'
    rw [Matrix.mul_one] at hm
    rw [hm]
    simp [hπ'1]
  have hfun : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v)) =
      fun t : ℝ => J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := funext he
  rw [hfun]
  have hhg : h * g ∈ Glev k r (Fin.last r) ∩ D := by
    refine ⟨sv_uw_glev hh hg.1, ?_⟩
    have := hD.2 g hg h (sv_uw_slev hh _) 1 (sv_uw_slev h1' _)
    simpa using this
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hJ.1 (h * g) hhg
  have hd : DifferentiableAt ℝ F (h * g) :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hc : HasDerivAt (fun t : ℝ => h * NormedSpace.exp ((t : ℂ) • X) * g)
      (mulRightRealCLM g (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X)) 0 :=
    (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (B5.curve_hasDerivAt h X 0)
  have hc0 : h * g = h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g := by
    simp [NormedSpace.exp_zero]
  have hFc : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g)) 0 :=
    (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).differentiableAt
  have hFv : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g) v) 0 :=
    ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hFc
  refine hFv.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, h * NormedSpace.exp ((t : ℂ) • X) * g ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [← hc0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with t ht
  rw [hFe _ ht (sv_uw_glev (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) hg.1)]

end SmoothJ

section Conj

variable {k r : ℕ}

/- English proof (translation)
Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh₀.1`. Establish `hi1 : h₀ * h₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `hU : h₀ᴴ * Hpk k r * h₀ = Hpk k r` using `hh₀.1`. Establish `A : (h₀⁻¹)ᴴ * Hpk k r = Hpk k r * h₀`. Combine the equalities or inequalities in the displayed calculation.

Establish `B : Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = h₀ᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * h₀ := by`. Rewrite using `[A, B]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hX.1]; simp`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₀.2.2, hX.2.1, Matrix.mulVec_zero]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).1, (hX.2.2 a).1, Matrix.mulVec_zero]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).2, (hX.2.2 a).2, Matrix.mulVec_zero]`.
-/
theorem sv_lie_conj {z : Fin (2 * r + k + 1) → ℂ} {X h₀ : Mx k r} (hX : inLieW k r z X)
    (hh₀ : h₀ ∈ UWset k r z) : inLieW k r z (h₀⁻¹ * X * h₀) := by
  have hu := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hi1 : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : h₀ᴴ * Hpk k r * h₀ = Hpk k r := hh₀.1
  have A : (h₀⁻¹)ᴴ * Hpk k r = Hpk k r * h₀ := by
    calc (h₀⁻¹)ᴴ * Hpk k r = (h₀⁻¹)ᴴ * (h₀ᴴ * Hpk k r * h₀) := by rw [hU]
      _ = (h₀ * h₀⁻¹)ᴴ * Hpk k r * h₀ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * h₀ := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r := by
    calc Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r * h₀ * h₀⁻¹ := by rw [hU]
      _ = h₀ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  refine ⟨?_, ?_, fun a => ⟨?_, ?_⟩⟩
  · calc (h₀⁻¹ * X * h₀)ᴴ * Hpk k r + Hpk k r * (h₀⁻¹ * X * h₀)
        = h₀ᴴ * (Xᴴ * ((h₀⁻¹)ᴴ * Hpk k r)) + (Hpk k r * h₀⁻¹) * X * h₀ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = h₀ᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * h₀ := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hX.1]; simp
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₀.2.2, hX.2.1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).1, (hX.2.2 a).1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).2, (hX.2.2 a).2, Matrix.mulVec_zero]

/- English proof (translation)
Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh₀.1`. Establish `hu' : IsUnit h₀` using `(Matrix.isUnit_iff_isUnit_det _).2 hu`. Establish `hi1 : h₀ * h₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `e : (t : ℂ) • (h₀⁻¹ * X * h₀) = h₀⁻¹ * ((t : ℂ) • X) * h₀`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.

Rewrite using `[e, Matrix.exp_conj' _ _ hu']`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc h h₀ h₀⁻¹, hi1, Matrix.mul_one]`.
-/
theorem sv_exp_conj {z : Fin (2 * r + k + 1) → ℂ} {X h h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) (t : ℝ) :
    h * NormedSpace.exp ((t : ℂ) • X) * h₀ = h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀)) := by
  have hu := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hu' : IsUnit h₀ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  have hi1 : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (t : ℂ) • (h₀⁻¹ * X * h₀) = h₀⁻¹ * ((t : ℂ) • X) * h₀ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj' _ _ hu']
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc h h₀ h₀⁻¹, hi1, Matrix.mul_one]

end Conj

section Lin

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

def svSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) : Submodule ℂ Wp where
  carrier := SmVec k r z π
  zero_mem' := by
    intro h _ X _
    simp only [map_zero]
    exact differentiableAt_const _
  add_mem' := by
    intro x y hx hy h hh X hX
    simp only [map_add]
    exact (hx h hh X hX).add (hy h hh X hX)
  smul_mem' := by
    intro c x hx h hh X hX
    simp only [map_smul]
    exact (hx h hh X hX).const_smul c

/- English proof (translation)
Introduce `h hh X hX`. Establish `e : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (π h₀ x)) = fun t : ℝ => π (h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀))) x`. Use function extensionality and compare the values at `t`. Rewrite using `[← sv_exp_conj hh₀ t, hrep.2 _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) _ hh₀]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `hx (h * h₀) (WeylGroupFacts.uw_mul hh hh₀) _ (sv_lie_conj hX hh₀)`.
-/
theorem sv_stable (hrep : IsCRepOn (UWset k r z) π) {h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) {x : Wp}
    (hx : x ∈ SmVec k r z π) : π h₀ x ∈ SmVec k r z π := by
  intro h hh X hX
  have e : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (π h₀ x)) =
      fun t : ℝ => π (h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀))) x := by
    funext t
    rw [← sv_exp_conj hh₀ t, hrep.2 _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) _ hh₀]
    rfl
  rw [e]
  exact hx (h * h₀) (WeylGroupFacts.uw_mul hh hh₀) _ (sv_lie_conj hX hh₀)

/- English proof (translation)
Break down `hπ.2.2.2.2.1 (svSub k r z π) (fun h hh v hv => sv_stable hπ.2.1 hh hv) with h0 | htop` into its components or cases. Establish `hm : x₀ ∈ svSub k r z π` using `hsm`. Rewrite `hm` using `[h0]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 hm) hx₀`. Establish `hm : v ∈ svSub k r z π` using `by rw [htop]; exact Submodule.mem_top`.

Conclude with `hm`.
-/
theorem sv_all {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    (v : Wp) : v ∈ SmVec k r z π := by
  rcases hπ.2.2.2.2.1 (svSub k r z π) (fun h hh v hv => sv_stable hπ.2.1 hh hv) with h0 | htop
  · have hm : x₀ ∈ svSub k r z π := hsm
    rw [h0] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hx₀
  · have hm : v ∈ svSub k r z π := by rw [htop]; exact Submodule.mem_top
    exact hm

/- English proof (translation)
Use `hall v 1 (sv_one_uw z) X hX` as an intermediate fact. Simplify `this` using `only [Matrix.one_mul]`.
-/
theorem sv_dRep_diff (hall : ∀ v : Wp, v ∈ SmVec k r z π) {X : Mx k r} (hX : inLieW k r z X) (v : Wp) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) 0 := by
  have := hall v 1 (sv_one_uw z) X hX
  simpa only [Matrix.one_mul] using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Unfold `dRep`. Simplify using `only [map_add]`. Conclude with `deriv_add (sv_dRep_diff hall hX x) (sv_dRep_diff hall hX y)`.

Introduce `c x`. Unfold `dRep`. Simplify using `only [map_smul]`. Conclude with `deriv_const_smul c (sv_dRep_diff hall hX x)`.
-/
theorem sv_dRep_lin (hall : ∀ v : Wp, v ∈ SmVec k r z π) {X : Mx k r} (hX : inLieW k r z X) :
    IsLinearMap ℂ (dRep π X) := by
  constructor
  · intro x y
    unfold dRep
    simp only [map_add]
    exact deriv_add (sv_dRep_diff hall hX x) (sv_dRep_diff hall hX y)
  · intro c x
    unfold dRep
    simp only [map_smul]
    exact deriv_const_smul c (sv_dRep_diff hall hX x)

/- English proof (translation)
Establish `l1` using `sv_dRep_lin hall h1`. Establish `l2` using `sv_dRep_lin hall h2`. Prove the components needed by the constructor for the conclusion. Introduce `x y`. Unfold `EcRep`.

Rewrite using `[l1.map_add, l2.map_add, smul_add]`. Normalize the expressions using the abelian group laws. Introduce `c x`. Unfold `EcRep`. Rewrite using `[l1.map_smul, l2.map_smul, smul_add, smul_comm Complex.I c]`.
-/
theorem sv_ecRep_lin (hall : ∀ v : Wp, v ∈ SmVec k r z π) {Z : Mx k r}
    (h1 : inLieW k r z (hpart1 (Hpk k r) Z)) (h2 : inLieW k r z (hpart2 (Hpk k r) Z)) :
    IsLinearMap ℂ (EcRep (Hpk k r) π Z) := by
  have l1 := sv_dRep_lin hall h1
  have l2 := sv_dRep_lin hall h2
  constructor
  · intro x y
    unfold EcRep
    rw [l1.map_add, l2.map_add, smul_add]
    abel
  · intro c x
    unfold EcRep
    rw [l1.map_smul, l2.map_smul, smul_add, smul_comm Complex.I c]

end Lin

section Frame

variable {k r : ℕ}

/- English proof (translation)
Simplify using `[herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem sv_herm_bvec (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Rewrite using `[sv_herm_bvec]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`. Rewrite using `[hw i hi, star_zero, zero_mul]`. Establish `h0 : Hpk k r i p = 0`.

Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[h0, mul_zero]`.
-/
theorem sv_herm_out {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) {p : Fin (2 * r + k + 1)}
    (hp : p.val < r ∨ r + k < p.val) : herm (Hpk k r) (bvec p) w = 0 := by
  rw [sv_herm_bvec]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hw i hi, star_zero, zero_mul]
  · have h0 : Hpk k r i p = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, mul_zero]

/- English proof (translation)
Establish `hsym : ∀ i j, Hpk k r i j = Hpk k r j i`. Introduce `i j`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hreal : ∀ i j, star (Hpk k r i j) = Hpk k r i j`.

Introduce `i j`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hreal]`. Repeatedly rewrite using `[Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsym]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sv_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  have hsym : ∀ i j, Hpk k r i j = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hreal : ∀ i j, star (Hpk k r i j) = Hpk k r i j := by
    intro i j
    simp only [Hpk]
    split_ifs <;> simp
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hreal]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym]
  ring

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [Matrix.mulVec, dotProduct, unitB, Matrix.of_apply, sv_herm_bvec, Pi.smul_apply, smul_eq_mul]`. Unfold `herm`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sv_unitB_mulVec {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) : unitB (Hpk k r) Bs a b *ᵥ v = herm (Hpk k r) v (Bs b) • Bs a := by
  ext p
  simp only [Matrix.mulVec, dotProduct, unitB, Matrix.of_apply, sv_herm_bvec, Pi.smul_apply, smul_eq_mul]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.star_apply]
  ring

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, unitB, Matrix.of_apply, star_mul', Pi.smul_apply, smul_eq_mul]`. Unfold `herm`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.star_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sv_unitB_adj {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ v) =
      herm (Hpk k r) v (Bs a) • fun p => star (herm (Hpk k r) (bvec p) (Bs b)) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, unitB, Matrix.of_apply, star_mul',
    Pi.smul_apply, smul_eq_mul]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply]
  ring

/- English proof (translation)
Establish `e1 : unitB (Hpk k r) Bs a b *ᵥ v = 0` using `by rw [sv_unitB_mulVec, hb, zero_smul]`. Establish `e2 : (Hpk k r * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ v = 0`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sv_unitB_adj, ha, zero_smul, Matrix.mulVec_zero]`. Unfold `hpart1 hpart2`. Rewrite using `[Qx2.hpk_inv, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, e1, e2]`.

Simplify using `only [sub_self, add_zero, smul_zero, and_self]`.
-/
theorem sv_unitB_kill {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    {v : Fin (2 * r + k + 1) → ℂ} (ha : herm (Hpk k r) v (Bs a) = 0) (hb : herm (Hpk k r) v (Bs b) = 0) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧ hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 := by
  have e1 : unitB (Hpk k r) Bs a b *ᵥ v = 0 := by rw [sv_unitB_mulVec, hb, zero_smul]
  have e2 : (Hpk k r * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sv_unitB_adj, ha, zero_smul, Matrix.mulVec_zero]
  unfold hpart1 hpart2
  rw [Qx2.hpk_inv, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, e1, e2]
  simp only [sub_self, add_zero, smul_zero, and_self]

/- English proof (translation)
Establish `hzB : ∀ x, herm (Hpk k r) z (Bs x) = 0` using `fun x => by`. Rewrite using `[sv_herm_swap, hBs.2.2 x z (List.mem_singleton_self z), star_zero]`. Establish `heB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (eI k r c)) (Bs x) = 0` using `fun c x => sv_herm_out (hBs.1 x) (Or.inl (by simp [eI]))`. Establish `hesB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (esI k r c)) (Bs x) = 0` using `fun c x => sv_herm_out (hBs.1 x) (Or.inr (by have := c.isLt; simp only [esI]; omega))`. Establish `kz` using `sv_unitB_kill Bs a b (hzB a) (hzB b)`.

Establish `ke` using `fun c => sv_unitB_kill Bs a b (heB c a) (heB c b)`. Establish `kes` using `fun c => sv_unitB_kill Bs a b (hesB c a) (hesB c b)`. Conclude with `⟨⟨Qx2.hpart1_lie _, kz.1, fun c => ⟨(ke c).1, (kes c).1⟩⟩, ⟨Qx2.hpart2_lie _, kz.2, fun c => ⟨(ke c).2, (kes c).2⟩⟩⟩`.
-/
theorem sv_unitB_lie {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [z] Bs) (a b : Fin m) :
    inLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hzB : ∀ x, herm (Hpk k r) z (Bs x) = 0 := fun x => by
    rw [sv_herm_swap, hBs.2.2 x z (List.mem_singleton_self z), star_zero]
  have heB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (eI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inl (by simp [eI]))
  have hesB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (esI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inr (by have := c.isLt; simp only [esI]; omega))
  have kz := sv_unitB_kill Bs a b (hzB a) (hzB b)
  have ke := fun c => sv_unitB_kill Bs a b (heB c a) (heB c b)
  have kes := fun c => sv_unitB_kill Bs a b (hesB c a) (hesB c b)
  exact ⟨⟨Qx2.hpart1_lie _, kz.1, fun c => ⟨(ke c).1, (kes c).1⟩⟩,
    ⟨Qx2.hpart2_lie _, kz.2, fun c => ⟨(ke c).2, (kes c).2⟩⟩⟩

end Frame

section QM

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨fun x y => rfl, fun c x => rfl⟩`. Consider the case `cons T L ih`. Establish `hT` using `hL T (by simp)`. Establish `ih'` using `ih (fun S hS => hL S (by simp [hS]))`.

Use `⟨fun x y => ?_, fun c x => ?_⟩` and prove the remaining obligations. Establish `e1` using `ih'.map_add x y`. Establish `e2` using `hT.map_add (List.foldr (fun T h => T h) x L) (List.foldr (fun T h => T h) y L)`. Apply the tactic sequence `try simp only at e1`. Simplify using `only [List.foldr_cons, e1, e2]`.

Establish `e1` using `ih'.map_smul c x`. Establish `e2` using `hT.map_smul c (List.foldr (fun T h => T h) x L)`. Apply the tactic sequence `try simp only at e1`. Simplify using `only [List.foldr_cons, e1, e2]`.
-/
theorem sv_foldr_lin {X : Type*} [AddCommGroup X] [Module ℂ X] (L : List (X → X))
    (hL : ∀ T ∈ L, IsLinearMap ℂ T) : IsLinearMap ℂ (fun x => L.foldr (fun T h => T h) x) := by
  induction L with
  | nil => exact ⟨fun x y => rfl, fun c x => rfl⟩
  | cons T L ih =>
    have hT := hL T (by simp)
    have ih' := ih (fun S hS => hL S (by simp [hS]))
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · have e1 := ih'.map_add x y
      have e2 := hT.map_add (List.foldr (fun T h => T h) x L) (List.foldr (fun T h => T h) y L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]
    · have e1 := ih'.map_smul c x
      have e2 := hT.map_smul c (List.foldr (fun T h => T h) x L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]

/- English proof (translation)
Establish `hfac : ∀ σ : Equiv.Perm (Fin t), IsLinearMap ℂ (fun x : X => (List.ofFn fun k : Fin t => fun y : X => (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr (fun T h => T h) x)`. Introduce `σ`. Apply `sv_foldr_lin` to reduce the goal to its premises. Introduce `T hT`. Rewrite `hT` using `[List.mem_ofFn]`.

Take `⟨j, rfl⟩` from `hT`. Establish `hl` using `hE (a (σ j)) (b j)`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `intro x y split_ifs <;> simp only [hl.map_add, smul_add] <;> abel`. Apply the tactic sequence `intro c x split_ifs <;> simp only [hl.map_smul, smul_add, zero_add, smul_comm c]`.

Prove the components needed by the constructor for the conclusion. Introduce `x y`. Unfold `qmF`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_add]`. Conclude with `congrArg _ ((hfac σ).map_add x y)`. Introduce `c x`. Unfold `qmF`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm c]`. Conclude with `congrArg _ ((hfac σ).map_smul c x)`.
-/
theorem sv_qmF_lin {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (hE : ∀ a b, IsLinearMap ℂ (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : IsLinearMap ℂ (qmF Eop a b u) := by
  have hfac : ∀ σ : Equiv.Perm (Fin t), IsLinearMap ℂ (fun x : X =>
      (List.ofFn fun k : Fin t => fun y : X =>
        (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr
        (fun T h => T h) x) := by
    intro σ
    apply sv_foldr_lin
    intro T hT
    rw [List.mem_ofFn] at hT
    obtain ⟨j, rfl⟩ := hT
    have hl := hE (a (σ j)) (b j)
    constructor
    · intro x y
      split_ifs <;> simp only [hl.map_add, smul_add] <;> abel
    · intro c x
      split_ifs <;> simp only [hl.map_smul, smul_add, zero_add, smul_comm c]
  constructor
  · intro x y
    unfold qmF
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hfac σ).map_add x y)
  · intro c x
    unfold qmF
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm c]
    exact congrArg _ ((hfac σ).map_smul c x)

end QM

section Cap

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

/- English proof (translation)
Establish `hall` using `sv_all hπ hx₀ hsm`. Unfold `capRep`. Conclude with `sv_qmF_lin _ (fun a b => sv_ecRep_lin hall (sv_unitB_lie hBs a b).1 (sv_unitB_lie hBs a b).2) id id w`.
-/
theorem capRep_linear {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [z] Bs) (w : ℂ) :
    IsLinearMap ℂ (capRep k r π Bs w) := by
  have hall := sv_all hπ hx₀ hsm
  unfold capRep
  exact sv_qmF_lin _ (fun a b => sv_ecRep_lin hall (sv_unitB_lie hBs a b).1 (sv_unitB_lie hBs a b).2) id id w

end Cap

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
