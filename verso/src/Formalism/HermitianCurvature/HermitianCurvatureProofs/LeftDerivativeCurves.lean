import Formalism.HermitianCurvature.StatementQr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftDerivativeCurves

open Qx2 (Good)

section Analysis

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def mulL {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulL_apply {n : ℕ} (X h : Matrix (Fin n) (Fin n) ℂ) : mulL X h = X * h := rfl

/- English proof (translation)
Establish `h0` using `Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt (1 : Mx k r) X 0`. Simplify using `only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h0`. Set `R : Mx k r →L[ℝ] Mx k r` to `LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)`. Conclude with `R.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0`.
-/
theorem lcurve_hasDeriv (X g : Mx k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
  have h0 := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h0
  let R : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)
  exact R.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lcurve_zero (X g : Mx k r) : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g = g := by
  simp

/- English proof (translation)
Establish `h1 : (1 : Mx k r) ∈ Glev k r i` using `⟨by show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp, fun a _ => ⟨by simp, by simp⟩⟩`. Establish `he` using `Qx2.curve_lev h1 hX t`. Rewrite `he` using `[Matrix.one_mul]`. Take `⟨he1, he2⟩` from `he`. Take `⟨hg1, hg2⟩` from `hg`.

Establish `he1' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r` using `he1`. Establish `hg1' : gᴴ * Hpk k r * g = Hpk k r` using `hg1`. Use `⟨?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show (NormedSpace.exp ((t : ℂ) • X) * g)ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) = Hpk k r`. Rewrite using `[conjTranspose_mul]`.

Establish `e : gᴴ * (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) = gᴴ * ((NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * g`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, he1', hg1']`. Take `⟨h1, h2⟩` from `hg2 a ha`. Take `⟨h3, h4⟩` from `he2 a ha`.

Conclude with `⟨by rw [← Matrix.mulVec_mulVec, h1, h3], by rw [← Matrix.mulVec_mulVec, h2, h4]⟩`.
-/
theorem lcurve_lev {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * g ∈ Glev k r i := by
  have h1 : (1 : Mx k r) ∈ Glev k r i :=
    ⟨by show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp, fun a _ => ⟨by simp, by simp⟩⟩
  have he := Qx2.curve_lev h1 hX t
  rw [Matrix.one_mul] at he
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hg1, hg2⟩ := hg
  have he1' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r := he1
  have hg1' : gᴴ * Hpk k r * g = Hpk k r := hg1
  refine ⟨?_, fun a ha => ?_⟩
  · show (NormedSpace.exp ((t : ℂ) • X) * g)ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) = Hpk k r
    rw [conjTranspose_mul]
    have e : gᴴ * (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * g) =
        gᴴ * ((NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * g := by
      simp only [Matrix.mul_assoc]
    rw [e, he1', hg1']
  · obtain ⟨h1, h2⟩ := hg2 a ha
    obtain ⟨h3, h4⟩ := he2 a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, h1, h3], by rw [← Matrix.mulVec_mulVec, h2, h4]⟩

/- English proof (translation)
Establish `hc` using `lcurve_hasDeriv X g`. Establish `h1` using `hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (lcurve_zero X g).symm`. Establish `hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) =ᶠ[𝓝 0] (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g))`. Establish `hU' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * g ∈ U`. Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises.

Establish `h0` using `hU.mem_nhds hgU`. Rewrite `h0` using `[← lcurve_zero X g]`. Conclude with `h0`. Use `filter_upwards [hU'] with t ht`. Conclude with `he _ ht (lcurve_lev hg hX t)`.

Conclude with `h1.congr_of_eventuallyEq hev`.
-/
theorem l_hasDeriv_ext {f F : Mx k r → E} {U : Set (Mx k r)} (hU : IsOpen U) {g X : Mx k r}
    (hgU : g ∈ U) (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (hF : DifferentiableAt ℝ F g)
    (he : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  have hc := lcurve_hasDeriv X g
  have h1 := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (lcurve_zero X g).symm
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) =ᶠ[𝓝 0]
      (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) := by
    have hU' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * g ∈ U := by
      apply hc.continuousAt.preimage_mem_nhds
      have h0 := hU.mem_nhds hgU
      rw [← lcurve_zero X g] at h0
      exact h0
    filter_upwards [hU'] with t ht
    exact he _ ht (lcurve_lev hg hX t)
  exact h1.congr_of_eventuallyEq hev

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g hg`. Establish `hFd : DifferentiableAt ℝ F g` using `(hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)`. Establish `h` using `l_hasDeriv_ext hU hgU hg.1 hX hFd he`. Unfold `LdV`. Rewrite using `[h.deriv]`.

Conclude with `h`.
-/
theorem ld_hasDeriv {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (LdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  have hFd : DifferentiableAt ℝ F g := (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  have h := l_hasDeriv_ext hU hgU hg.1 hX hFd he
  unfold LdV
  rw [h.deriv]
  exact h

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => fderiv ℝ F x (X * x), hU, hgU, ?_, fun x hxU hx => ?_⟩` and prove the remaining obligations. Establish `h2 : ContDiffOn ℝ ∞ (fun x : Mx k r => X * x) U` using `(mulL X).contDiff.contDiffOn`. Conclude with `(hF.fderiv_of_isOpen hU (by simp)).clm_apply h2`.

Establish `hFd : DifferentiableAt ℝ F x` using `(hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)`. Conclude with `(l_hasDeriv_ext hU hxU hx hX hFd he).deriv`.
-/
theorem ld_smooth {f : Mx k r → E} (hf : SmoothLev k r i D f) {X : Mx k r} (hX : inLieLev k r i X) :
    SmoothLev k r i D (LdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x (X * x), hU, hgU, ?_, fun x hxU hx => ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun x : Mx k r => X * x) U := (mulL X).contDiff.contDiffOn
    exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply h2
  · have hFd : DifferentiableAt ℝ F x := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    exact (l_hasDeriv_ext hU hxU hx hX hFd he).deriv

/- English proof (translation)
Establish `h1` using `ld_hasDeriv hf hg hX`. Establish `h2` using `ld_hasDeriv hf₂ hg hX`. Conclude with `(h1.add (h2.const_smul s)).deriv`.
-/
theorem ld_lin {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) (s : ℂ)
    {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) :
    LdV X (fun x => f x + s • f₂ x) g = LdV X f g + s • LdV X f₂ g := by
  have h1 := ld_hasDeriv hf hg hX
  have h2 := ld_hasDeriv hf₂ hg hX
  exact (h1.add (h2.const_smul s)).deriv

/- English proof (translation)
Use `⟨fun f hf => ld_smooth hf hX, fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ld_lin hf hf₂ s hx hX⟩` and prove the remaining obligations. Use `show deriv _ 0 = deriv _ 0`. Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Establish `hc` using `(lcurve_hasDeriv X x).continuousAt`. Establish `hD' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * x ∈ D`.

Apply `hc.preimage_mem_nhds` to reduce the goal to its premises. Establish `h0` using `hD.mem_nhds hx.2`. Rewrite `h0` using `[← lcurve_zero X x]`. Conclude with `h0`. Use `filter_upwards [hD'] with t ht`.

Conclude with `h _ ⟨lcurve_lev hx.1 hX t, ht⟩`.
-/
theorem good_ld (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r i X) :
    Good k r i D (fun f : Mx k r → E => LdV X f) := by
  refine ⟨fun f hf => ld_smooth hf hX, fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ld_lin hf hf₂ s hx hX⟩
  show deriv _ 0 = deriv _ 0
  apply Filter.EventuallyEq.deriv_eq
  have hc := (lcurve_hasDeriv X x).continuousAt
  have hD' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * x ∈ D := by
    apply hc.preimage_mem_nhds
    have h0 := hD.mem_nhds hx.2
    rw [← lcurve_zero X x] at h0
    exact h0
  filter_upwards [hD'] with t ht
  exact h _ ⟨lcurve_lev hx.1 hX t, ht⟩

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g hg`. Establish `hdF : ∀ x ∈ U, DifferentiableAt ℝ F x` using `fun x hx => (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)`. Establish `h1` using `hF.fderiv_of_isOpen (m := ∞) hU (by simp)`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ F) g` using `(h1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Establish `eL : ∀ x ∈ U, x ∈ Glev k r i → LdV X f x = fderiv ℝ F x (mulL X x)` using `fun x hx hxG => (l_hasDeriv_ext hU hx hxG hX (hdF x hx) he).deriv`.

Establish `eR : ∀ x ∈ U, x ∈ Glev k r i → RdV Y f x = fderiv ℝ F x (mulRightRealCLM Y x)` using `fun x hx hxG => (Qx2.hasDeriv_ext hU hx hxG hY (hdF x hx) he).deriv`. Establish `HL` using `hd.hasFDerivAt.clm_apply (mulL X).hasFDerivAt`. Establish `HR` using `hd.hasFDerivAt.clm_apply (mulRightRealCLM Y).hasFDerivAt`. Establish `a1 : RdV Y (LdV X f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulL X x)) g (g * Y)` using `(Qx2.hasDeriv_ext hU hgU hg.1 hY HL.differentiableAt eL).deriv`. Establish `a2 : LdV X (RdV Y f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulRightRealCLM Y x)) g (X * g)` using `(l_hasDeriv_ext hU hgU hg.1 hX HR.differentiableAt eR).deriv`.

Establish `hsym : IsSymmSndFDerivAt ℝ F g` using `(hF.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)`. Establish `b1` using `DFunLike.congr_fun HL.fderiv (g * Y)`. Establish `b2` using `DFunLike.congr_fun HR.fderiv (X * g)`. Use `a1.trans (b1.trans (Eq.trans ?_ (a2.trans b2).symm))` and prove the remaining obligations. Establish `h3` using `hsym (g * Y) (X * g)`.

Use `show fderiv ℝ F g (X * (g * Y)) + fderiv ℝ (fderiv ℝ F) g (g * Y) (X * g) = fderiv ℝ F g (X * g * Y) + fderiv ℝ (fderiv ℝ F) g (X * g) (g * Y)`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `congrArg (fun e => fderiv ℝ F g (X * (g * Y)) + e) h3`.
-/
theorem rd_ld_comm {f : Mx k r → E} (hf : SmoothLev k r i D f) {X Y g : Mx k r} (hX : inLieLev k r i X)
    (hY : inLieLev k r i Y) (hg : g ∈ Glev k r i ∩ D) :
    RdV Y (LdV X f) g = LdV X (RdV Y f) g := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  have hdF : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have h1 := hF.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) g := (h1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have eL : ∀ x ∈ U, x ∈ Glev k r i → LdV X f x = fderiv ℝ F x (mulL X x) := fun x hx hxG =>
    (l_hasDeriv_ext hU hx hxG hX (hdF x hx) he).deriv
  have eR : ∀ x ∈ U, x ∈ Glev k r i → RdV Y f x = fderiv ℝ F x (mulRightRealCLM Y x) := fun x hx hxG =>
    (Qx2.hasDeriv_ext hU hx hxG hY (hdF x hx) he).deriv
  have HL := hd.hasFDerivAt.clm_apply (mulL X).hasFDerivAt
  have HR := hd.hasFDerivAt.clm_apply (mulRightRealCLM Y).hasFDerivAt
  have a1 : RdV Y (LdV X f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulL X x)) g (g * Y) :=
    (Qx2.hasDeriv_ext hU hgU hg.1 hY HL.differentiableAt eL).deriv
  have a2 : LdV X (RdV Y f) g = fderiv ℝ (fun x => fderiv ℝ F x (mulRightRealCLM Y x)) g (X * g) :=
    (l_hasDeriv_ext hU hgU hg.1 hX HR.differentiableAt eR).deriv
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    (hF.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have b1 := DFunLike.congr_fun HL.fderiv (g * Y)
  have b2 := DFunLike.congr_fun HR.fderiv (X * g)
  refine a1.trans (b1.trans (Eq.trans ?_ (a2.trans b2).symm))
  have h3 := hsym (g * Y) (X * g)
  show fderiv ℝ F g (X * (g * Y)) + fderiv ℝ (fderiv ℝ F) g (g * Y) (X * g) =
    fderiv ℝ F g (X * g * Y) + fderiv ℝ (fderiv ℝ F) g (X * g) (g * Y)
  rw [Matrix.mul_assoc]
  exact congrArg (fun e => fderiv ℝ F g (X * (g * Y)) + e) h3

end Analysis

section Comm

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def Comm (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T S : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ f, SmoothLev k r i D f → ∀ x ∈ Glev k r i ∩ D, T (S f) x = S (T f) x

/- English proof (translation)
Introduce `f hf x hx` and use `(h f hf x hx).symm`.
-/
theorem Comm.symm {T S : (Mx k r → E) → Mx k r → E} (h : Comm k r i D T S) : Comm k r i D S T := fun f hf x hx => (h f hf x hx).symm

/- English proof (translation)
Introduce `f hf x hx` and use `rfl`.
-/
theorem comm_id (S : (Mx k r → E) → Mx k r → E) : Comm k r i D (fun f => f) S := fun f hf x hx => rfl

/- English proof (translation)
Introduce `f hf x hx`. Use `show T₁ (S f) x + c • T₂ (S f) x = S (fun y => T₁ f y + c • T₂ f y) x`. Rewrite using `[hS.lin _ _ c (hT₁.sm f hf) (hT₂.sm f hf) x hx, h₁ f hf x hx, h₂ f hf x hx]`.
-/
theorem Comm.lin {T₁ T₂ S : (Mx k r → E) → Mx k r → E} (hS : Good k r i D S) (hT₁ : Good k r i D T₁)
    (hT₂ : Good k r i D T₂) (h₁ : Comm k r i D T₁ S) (h₂ : Comm k r i D T₂ S) (c : ℂ) :
    Comm k r i D (fun f x => T₁ f x + c • T₂ f x) S := by
  intro f hf x hx
  show T₁ (S f) x + c • T₂ (S f) x = S (fun y => T₁ f y + c • T₂ f y) x
  rw [hS.lin _ _ c (hT₁.sm f hf) (hT₂.sm f hf) x hx, h₁ f hf x hx, h₂ f hf x hx]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact hf`. Consider the case `cons T L ih`. Conclude with `(hL T List.mem_cons_self).sm _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))`.
-/
private theorem smoothLev_foldr_of_good (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, Good k r i D T)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact (hL T List.mem_cons_self).sm _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact (comm_id B).symm`. Consider the case `cons T L ih`. Introduce `f hf x hx`. Establish `hT` using `hL T List.mem_cons_self`.

Establish `hL' : ∀ S ∈ L, Good k r i D S` using `fun S hS => hL S (List.mem_cons_of_mem _ hS)`. Establish `hc' : ∀ S ∈ L, Comm k r i D B S` using `fun S hS => hc S (List.mem_cons_of_mem _ hS)`. Use `show B (T (L.foldr (fun T h => T h) f)) x = T (L.foldr (fun T h => T h) (B f)) x`. Rewrite using `[hc T List.mem_cons_self _ (smoothLev_foldr_of_good L hL' f hf) x hx]`. Conclude with `hT.loc _ _ (fun y hy => ih hL' hc' f hf y hy) x hx`.
-/
theorem comm_foldr {B : (Mx k r → E) → Mx k r → E} (L : List ((Mx k r → E) → Mx k r → E))
    (hL : ∀ T ∈ L, Good k r i D T) (hc : ∀ T ∈ L, Comm k r i D B T) :
    Comm k r i D B (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact (comm_id B).symm
  | cons T L ih =>
    intro f hf x hx
    have hT := hL T List.mem_cons_self
    have hL' : ∀ S ∈ L, Good k r i D S := fun S hS => hL S (List.mem_cons_of_mem _ hS)
    have hc' : ∀ S ∈ L, Comm k r i D B S := fun S hS => hc S (List.mem_cons_of_mem _ hS)
    show B (T (L.foldr (fun T h => T h) f)) x = T (L.foldr (fun T h => T h) (B f)) x
    rw [hc T List.mem_cons_self _ (smoothLev_foldr_of_good L hL' f hf) x hx]
    exact hT.loc _ _ (fun y hy => ih hL' hc' f hf y hy) x hx

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => intro f _`. Both sides reduce to the same expression. Consider the case `cons p L ih`. Introduce `f hf`.

Establish `hA' : ∀ q ∈ L, Good k r i D q.1` using `fun q hq => hA q (List.mem_cons_of_mem _ hq)`. Establish `hB' : ∀ q ∈ L, Good k r i D q.2` using `fun q hq => hB q (List.mem_cons_of_mem _ hq)`. Establish `hpt' : ∀ q ∈ L, ∀ f, q.1 f g₀ = q.2 f g₀` using `fun q hq => hpt q (List.mem_cons_of_mem _ hq)`. Establish `hc' : ∀ q ∈ L, ∀ q' ∈ L, Comm k r i D q'.2 q.1` using `fun q hq q' hq' => hc q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')`. Establish `hcomm : Comm k r i D p.2 (fun f => (L.map Prod.fst).foldr (fun T h => T h) f)` using `comm_foldr _ (fun T hT => by obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT; exact hA' q hq) (fun T hT => by`.

Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hT`. Conclude with `hc q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)`. Conclude with `(hpt p List.mem_cons_self _).trans ((hcomm f hf g₀ hg₀).trans (ih hA' hB' hpt' hc' (p.2 f) ((hB p List.mem_cons_self).sm f hf)))`.
-/
theorem swap_list {g₀ : Mx k r} (hg₀ : g₀ ∈ Glev k r i ∩ D)
    (L : List (((Mx k r → E) → Mx k r → E) × ((Mx k r → E) → Mx k r → E)))
    (hA : ∀ p ∈ L, Good k r i D p.1) (hB : ∀ p ∈ L, Good k r i D p.2)
    (hpt : ∀ p ∈ L, ∀ f, p.1 f g₀ = p.2 f g₀) (hc : ∀ p ∈ L, ∀ q ∈ L, Comm k r i D q.2 p.1) :
    ∀ f, SmoothLev k r i D f →
      (L.map Prod.fst).foldr (fun T h => T h) f g₀ = (L.map Prod.snd).foldl (fun h T => T h) f g₀ := by
  induction L with
  | nil => intro f _; rfl
  | cons p L ih =>
    intro f hf
    have hA' : ∀ q ∈ L, Good k r i D q.1 := fun q hq => hA q (List.mem_cons_of_mem _ hq)
    have hB' : ∀ q ∈ L, Good k r i D q.2 := fun q hq => hB q (List.mem_cons_of_mem _ hq)
    have hpt' : ∀ q ∈ L, ∀ f, q.1 f g₀ = q.2 f g₀ := fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    have hc' : ∀ q ∈ L, ∀ q' ∈ L, Comm k r i D q'.2 q.1 := fun q hq q' hq' =>
      hc q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')
    have hcomm : Comm k r i D p.2 (fun f => (L.map Prod.fst).foldr (fun T h => T h) f) :=
      comm_foldr _ (fun T hT => by obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT; exact hA' q hq)
        (fun T hT => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
          exact hc q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)
    exact (hpt p List.mem_cons_self _).trans ((hcomm f hf g₀ hg₀).trans
      (ih hA' hB' hpt' hc' (p.2 f) ((hB p List.mem_cons_self).sm f hf)))

def rop (k r : ℕ) (c : ℂ) (Z : Mx k r) (f : Mx k r → E) : Mx k r → E := fun x => RZ (Hpk k r) Z f x + c • f x

def lop (k r : ℕ) (c : ℂ) (Z : Mx k r) (f : Mx k r → E) : Mx k r → E := fun x => LZ (Hpk k r) Z f x + c • f x

/- English proof (translation)
Conclude with `(Qx2.good_rd hD h1).add ((Qx2.good_rd hD h2).smul Complex.I)`.
-/
theorem good_RZ (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) : Good k r i D (RZ (E := E) (Hpk k r) Z) := by
  exact (Qx2.good_rd hD h1).add ((Qx2.good_rd hD h2).smul Complex.I)

/- English proof (translation)
Conclude with `(good_ld hD h1).add ((good_ld hD h2).smul Complex.I)`.
-/
theorem good_LZ (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) : Good k r i D (LZ (E := E) (Hpk k r) Z) := by
  exact (good_ld hD h1).add ((good_ld hD h2).smul Complex.I)

/- English proof (translation)
Conclude with `(good_RZ hD h1 h2).add (Qx2.good_id.smul c)`.
-/
theorem good_rop (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (c : ℂ) : Good k r i D (rop (E := E) k r c Z) := by
  exact (good_RZ hD h1 h2).add (Qx2.good_id.smul c)

/- English proof (translation)
Conclude with `(good_LZ hD h1 h2).add (Qx2.good_id.smul c)`.
-/
theorem good_lop (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (c : ℂ) : Good k r i D (lop (E := E) k r c Z) := by
  exact (good_LZ hD h1 h2).add (Qx2.good_id.smul c)

/- English proof (translation)
Introduce `f hf x hx` and use `rd_ld_comm hf hX hY hx`.
-/
theorem comm_rd_ld {X Y : Mx k r} (hX : inLieLev k r i X) (hY : inLieLev k r i Y) :
    Comm (E := E) k r i D (fun f => RdV Y f) (fun f => LdV X f) := fun f hf x hx => rd_ld_comm hf hX hY hx

/- English proof (translation)
Establish `hR : ∀ Y, inLieLev k r i Y → Comm (E` using `E) k r i D (LZ (Hpk k r) Z) (fun f => RdV Y f) := fun Y hY => Comm.lin (Qx2.good_rd hD hY) (good_ld hD h1) (good_ld hD h2) (comm_rd_ld h1 hY).symm (comm_rd_ld h2 hY).symm Complex.I`. Conclude with `Comm.lin (good_LZ hD h1 h2) (Qx2.good_rd hD h1') (Qx2.good_rd hD h2') (hR _ h1').symm (hR _ h2').symm Complex.I`.
-/
theorem comm_RZ_LZ (hD : IsOpen D) {Z Z' : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (h1' : inLieLev k r i (hpart1 (Hpk k r) Z'))
    (h2' : inLieLev k r i (hpart2 (Hpk k r) Z')) :
    Comm (E := E) k r i D (RZ (Hpk k r) Z') (LZ (Hpk k r) Z) := by
  have hR : ∀ Y, inLieLev k r i Y → Comm (E := E) k r i D (LZ (Hpk k r) Z) (fun f => RdV Y f) := fun Y hY =>
    Comm.lin (Qx2.good_rd hD hY) (good_ld hD h1) (good_ld hD h2) (comm_rd_ld h1 hY).symm
      (comm_rd_ld h2 hY).symm Complex.I
  exact Comm.lin (good_LZ hD h1 h2) (Qx2.good_rd hD h1') (Qx2.good_rd hD h2') (hR _ h1').symm (hR _ h2').symm
    Complex.I

/- English proof (translation)
Establish `h` using `Comm.lin (E := E) (good_LZ hD h1 h2) (good_RZ hD h1' h2') Qx2.good_id (comm_RZ_LZ hD h1 h2 h1' h2') (comm_id _) c'`. Conclude with `Comm.lin (good_rop hD h1' h2' c') (good_LZ hD h1 h2) Qx2.good_id h.symm (comm_id _) c`.
-/
theorem comm_lop_rop (hD : IsOpen D) {Z Z' : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (h1' : inLieLev k r i (hpart1 (Hpk k r) Z'))
    (h2' : inLieLev k r i (hpart2 (Hpk k r) Z')) (c c' : ℂ) :
    Comm (E := E) k r i D (lop k r c Z) (rop k r c' Z') := by
  have h := Comm.lin (E := E) (good_LZ hD h1 h2) (good_RZ hD h1' h2') Qx2.good_id (comm_RZ_LZ hD h1 h2 h1' h2')
    (comm_id _) c'
  exact Comm.lin (good_rop hD h1' h2' c') (good_LZ hD h1 h2) Qx2.good_id h.symm (comm_id _) c

end Comm

section Conj

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}

/- English proof (translation)
Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg, Qx2.hpk_sq']`. Rewrite using `[Matrix.inv_eq_left_inv hl, hl]`.
-/
theorem uh_inv_mul {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  rw [Matrix.inv_eq_left_inv hl, hl]

/- English proof (translation)
Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg, Qx2.hpk_sq']`. Conclude with `Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)`.
-/
theorem uh_mul_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)

/- English proof (translation)
Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg, Qx2.hpk_sq']`. Establish `hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]`. Rewrite using `[Matrix.inv_eq_left_inv hl]`.

Simplify using `only [Matrix.mul_assoc, hsq]`.
-/
theorem unitary_hermitian_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  have hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]
  rw [Matrix.inv_eq_left_inv hl]
  simp only [Matrix.mul_assoc, hsq]

/- English proof (translation)
Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg, Qx2.hpk_sq']`. Establish `hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]`. Rewrite using `[Matrix.inv_eq_left_inv hl]`.

Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Qx2.hpk_h, Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]`.
-/
theorem unitary_inv_conjTranspose_hermitian {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  have hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]
  rw [Matrix.inv_eq_left_inv hl]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Qx2.hpk_h, Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]

/- English proof (translation)
Establish `hl : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg, Qx2.hpk_sq']`. Establish `hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]`. Rewrite using `[Matrix.inv_eq_left_inv hl]`.

Simplify using `only [Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]`.
-/
theorem unitary_hermitian_conjTranspose {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : Hpk k r * gᴴ = g⁻¹ * Hpk k r := by
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [Matrix.mul_assoc], hg,
      Qx2.hpk_sq']
  have hsq : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul]
  rw [Matrix.inv_eq_left_inv hl]
  simp only [Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Matrix.inv_eq_left_inv Qx2.hpk_sq', conjTranspose_mul, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[unitary_inv_conjTranspose_hermitian hg, ← Matrix.mul_assoc (Hpk k r) gᴴ, unitary_hermitian_conjTranspose hg]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem adj_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    (Hpk k r)⁻¹ * (g⁻¹ * Z * g)ᴴ * Hpk k r = g⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * g := by
  rw [Matrix.inv_eq_left_inv Qx2.hpk_sq', conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [unitary_inv_conjTranspose_hermitian hg, ← Matrix.mul_assoc (Hpk k r) gᴴ, unitary_hermitian_conjTranspose hg]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[adj_conj hg]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem hpart1_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart1 (Hpk k r) (g⁻¹ * Z * g) = g⁻¹ * hpart1 (Hpk k r) Z * g := by
  unfold hpart1
  rw [adj_conj hg]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[adj_conj hg]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem hpart2_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart2 (Hpk k r) (g⁻¹ * Z * g) = g⁻¹ * hpart2 (Hpk k r) Z * g := by
  unfold hpart2
  rw [adj_conj hg]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Take `⟨hgU, hfix⟩` from `hg`. Take `⟨hXs, hXk⟩` from `hX`. Use `⟨?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, conjTranspose_mul]`. Establish `e1 : gᴴ * (Xᴴ * (g⁻¹)ᴴ) * Hpk k r = gᴴ * (Xᴴ * Hpk k r) * g`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[unitary_inv_conjTranspose_hermitian hgU]`. Establish `e2 : Hpk k r * (g⁻¹ * X * g) = gᴴ * (Hpk k r * X) * g`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[unitary_hermitian_inv hgU]`.

Rewrite using `[e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hXs, Matrix.mul_zero, Matrix.zero_mul]`. Take `⟨h1, h2⟩` from `hfix a ha`. Take `⟨h3, h4⟩` from `hXk a ha`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]`.

Rewrite using `[← Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]`.
-/
theorem lie_conj {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) :
    inLieLev k r i (g⁻¹ * X * g) := by
  obtain ⟨hgU, hfix⟩ := hg
  obtain ⟨hXs, hXk⟩ := hX
  refine ⟨?_, fun a ha => ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul]
    have e1 : gᴴ * (Xᴴ * (g⁻¹)ᴴ) * Hpk k r = gᴴ * (Xᴴ * Hpk k r) * g := by
      simp only [Matrix.mul_assoc]
      rw [unitary_inv_conjTranspose_hermitian hgU]
    have e2 : Hpk k r * (g⁻¹ * X * g) = gᴴ * (Hpk k r * X) * g := by
      simp only [← Matrix.mul_assoc]
      rw [unitary_hermitian_inv hgU]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hXs, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨h1, h2⟩ := hfix a ha
    obtain ⟨h3, h4⟩ := hXk a ha
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]

/- English proof (translation)
Establish `h1` using `uh_inv_mul hg`. Establish `h2` using `uh_mul_inv hg`. Establish `hu : IsUnit g` using `⟨⟨g, g⁻¹, h2, h1⟩, rfl⟩`. Rewrite using `[show (t : ℂ) • (g⁻¹ * X * g) = g⁻¹ * ((t : ℂ) • X) * g by rw [Matrix.mul_smul, Matrix.smul_mul]]`. Rewrite using `[Matrix.exp_conj' g _ hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
theorem exp_swap {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (X : Mx k r) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • (g⁻¹ * X * g)) = NormedSpace.exp ((t : ℂ) • X) * g := by
  have h1 := uh_inv_mul hg
  have h2 := uh_mul_inv hg
  have hu : IsUnit g := ⟨⟨g, g⁻¹, h2, h1⟩, rfl⟩
  rw [show (t : ℂ) • (g⁻¹ * X * g) = g⁻¹ * ((t : ℂ) • X) * g by rw [Matrix.mul_smul, Matrix.smul_mul]]
  rw [Matrix.exp_conj' g _ hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/- English proof (translation)
Simplify using `only [RdV, LdV, exp_swap hg]`.
-/
theorem rd_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (X : Mx k r) (F : Mx k r → E) :
    RdV (g⁻¹ * X * g) F g = LdV X F g := by
  simp only [RdV, LdV, exp_swap hg]

/- English proof (translation)
Simplify using `only [RZ, LZ, hpart1_conj hg, hpart2_conj hg, rd_conj hg]`.
-/
theorem RZ_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) (F : Mx k r → E) :
    RZ (Hpk k r) (g⁻¹ * Z * g) F g = LZ (Hpk k r) Z F g := by
  simp only [RZ, LZ, hpart1_conj hg, hpart2_conj hg, rd_conj hg]

/- English proof (translation)
Establish `hinv : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_left_inv Qx2.hpk_sq'`. Establish `hh : (Hpk k r)ᴴ = Hpk k r` using `Qx2.hpk_h`. Establish `hsq : Hpk k r * Hpk k r = 1` using `Qx2.hpk_sq'`. Establish `hsq' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X`. Introduce `X`.

Rewrite using `[← Matrix.mul_assoc, hsq, Matrix.one_mul]`. Establish `hout : ∀ a : Fin r, a.val < i.val → ¬ Qx2.inV k r i (eI k r a) ∧ ¬ Qx2.inV k r i (esI k r a)`. Introduce `a ha`. Use `i.isLt` as an intermediate fact. Simplify using `only [Qx2.inV, eI, esI, Fin.val_mk]`.

Use linear arithmetic over natural numbers and integers. Establish `h2I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2`. Establish `h : (2 * Complex.I) * (-Complex.I / 2) = 1`. Take the linear combination `(-1 : ℂ) * Complex.I_sq`. Conclude with `(eq_one_div_of_mul_eq_one_right h).symm`.

Establish `hst1 : star (1 / 2 : ℂ) = 1 / 2`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hst2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I))`. Rewrite using `[h2I]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`.

Use `⟨⟨?_, fun a ha => ?_⟩, ⟨?_, fun a ha => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [hpart1, hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hsq, hsq', Matrix.mul_one, hst1] module`. Take `⟨h1, h2⟩` from `hout a ha`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h1).1, (hZ _ h1).2, sub_zero, smul_zero]`.

Rewrite using `[hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h2).1, (hZ _ h2).2, sub_zero, smul_zero]`. Simplify using `only [hpart2, hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hsq, hsq', Matrix.mul_one, hst2] module`. Take `⟨h1, h2⟩` from `hout a ha`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h1).1, (hZ _ h1).2, add_zero, smul_zero]`.

Rewrite using `[hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h2).1, (hZ _ h2).2, add_zero, smul_zero]`.
-/
private theorem inLieLev_herm_components_of_mulVec_bvec_eq_zero {k r : ℕ} {i : Fin (r + 1)} {Z : Mx k r}
    (hZ : ∀ p, ¬ Qx2.inV k r i p → Z *ᵥ bvec p = 0 ∧ (Hpk k r * Zᴴ * Hpk k r) *ᵥ bvec p = 0) :
    inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z) := by
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Qx2.hpk_sq'
  have hh : (Hpk k r)ᴴ = Hpk k r := Qx2.hpk_h
  have hsq : Hpk k r * Hpk k r = 1 := Qx2.hpk_sq'
  have hsq' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hsq, Matrix.one_mul]
  have hout : ∀ a : Fin r, a.val < i.val → ¬ Qx2.inV k r i (eI k r a) ∧ ¬ Qx2.inV k r i (esI k r a) := by
    intro a ha
    have := i.isLt
    simp only [Qx2.inV, eI, esI, Fin.val_mk]
    omega
  have h2I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    have h : (2 * Complex.I) * (-Complex.I / 2) = 1 := by
      linear_combination (-1 : ℂ) * Complex.I_sq
    exact (eq_one_div_of_mul_eq_one_right h).symm
  have hst1 : star (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext <;> simp
  have hst2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [h2I]
    apply Complex.ext <;> simp <;> norm_num
  refine ⟨⟨?_, fun a ha => ?_⟩, ⟨?_, fun a ha => ?_⟩⟩
  · simp only [hpart1, hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst1]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h1).1, (hZ _ h1).2, sub_zero, smul_zero]
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h2).1, (hZ _ h2).2, sub_zero, smul_zero]
  · simp only [hpart2, hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst2]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h1).1, (hZ _ h1).2, add_zero, smul_zero]
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h2).1, (hZ _ h2).2, add_zero, smul_zero]

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hcol : ∀ (M : Mx k r) (x y : Fin (2 * r + k + 1)), (M *ᵥ bvec x) y = M y x`. Introduce `M x y`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hz : ∀ x y : Fin (2 * r + k + 1), (r ≤ x.val ∧ x.val ≤ r + k) → ¬ Qx2.inV k r i y → Hpk k r x y = 0`.

Introduce `x y hx hy`. Simplify using `only [Qx2.inV] at hy`. Establish `hne : x ≠ y`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Hpk, hne, and_false, ↓reduceIte]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Establish `hherm : herm (Hpk k r) (bvec p) (Bs b) = 0`. Unfold `herm`. Simplify using `only [dotProduct, hcol]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `y _`. Distinguish the cases in `hy : y.val < r ∨ r + k < y.val`. Simplify using `[hB b y hy]`. Rewrite using `[hz y p (by omega) hp, mul_zero]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `q`. Rewrite using `[hcol]`. Simplify using `[unitB, hherm]`. Use extensionality with `q`.

Rewrite using `[hcol, Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `y _`. Distinguish the cases in `hy : y.val < r ∨ r + k < y.val`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]`.

Introduce `x _`. Simplify using `[unitB, Matrix.conjTranspose_apply, hB a y hy]`. Rewrite using `[hz y p (by omega) hp, mul_zero]`.
-/
private theorem unitB_mulVec_bvec_eq_zero_of_not_inV {k r m : ℕ} {i : Fin (r + 1)} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) (p : Fin (2 * r + k + 1)) (hp : ¬ Qx2.inV k r i p) :
    unitB (Hpk k r) Bs a b *ᵥ bvec p = 0 ∧
      (Hpk k r * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
  have hi := i.isLt
  have hcol : ∀ (M : Mx k r) (x y : Fin (2 * r + k + 1)), (M *ᵥ bvec x) y = M y x := by
    intro M x y
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : ∀ x y : Fin (2 * r + k + 1), (r ≤ x.val ∧ x.val ≤ r + k) → ¬ Qx2.inV k r i y → Hpk k r x y = 0 := by
    intro x y hx hy
    simp only [Qx2.inV] at hy
    have hne : x ≠ y := by
      rintro rfl
      omega
    simp only [Hpk, hne, and_false, ↓reduceIte]
    rw [if_neg (by omega), if_neg (by omega)]
  have hherm : herm (Hpk k r) (bvec p) (Bs b) = 0 := by
    unfold herm
    simp only [dotProduct, hcol]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y.val < r ∨ r + k < y.val
    · simp [hB b y hy]
    · rw [hz y p (by omega) hp, mul_zero]
  refine ⟨?_, ?_⟩
  · ext q
    rw [hcol]
    simp [unitB, hherm]
  · ext q
    rw [hcol, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y.val < r ∨ r + k < y.val
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro x _
      simp [unitB, Matrix.conjTranspose_apply, hB a y hy]
    · rw [hz y p (by omega) hp, mul_zero]

/- English proof (translation)
Establish `hgU : g₀ ∈ UH (Hpk k r)` using `hg₀.1.1`. Establish `hZ : ∀ l, inLieLev k r i (hpart1 (Hpk k r) (Zs l)) ∧ inLieLev k r i (hpart2 (Hpk k r) (Zs l))`. Introduce `l`. Rewrite using `[hconj l, LeftDerivativeCurves.hpart1_conj hgU, LeftDerivativeCurves.hpart2_conj hgU]`. Conclude with `⟨LeftDerivativeCurves.lie_conj hg₀.1 (hW l).1, LeftDerivativeCurves.lie_conj hg₀.1 (hW l).2⟩`.

Set `A : Fin n → (Mx k r → E) → Mx k r → E` to `fun l y => (if ps l then cs l • y else 0) + RZ (Hpk k r) (Zs l) y`. Set `B : Fin n → (Mx k r → E) → Mx k r → E` to `fun l y => (if ps l then cs l • y else 0) + LZ (Hpk k r) (Ws l) y`. Establish `hAg : ∀ l, Qx2.Good k r i D (A l)`. Introduce `l`. Distinguish the cases in `h : ps l`.

Simplify using `only [A, h, ↓reduceIte]`. Conclude with `(Qx2.good_id.smul (cs l)).add (LeftDerivativeCurves.good_RZ hD (hZ l).1 (hZ l).2)`. Simplify using `only [A, h, ↓reduceIte, zero_add]`. Conclude with `LeftDerivativeCurves.good_RZ hD (hZ l).1 (hZ l).2`. Establish `hBg : ∀ l, Qx2.Good k r i D (B l)`.

Introduce `l`. Distinguish the cases in `h : ps l`. Simplify using `only [B, h, ↓reduceIte]`. Conclude with `(Qx2.good_id.smul (cs l)).add (LeftDerivativeCurves.good_LZ hD (hW l).1 (hW l).2)`. Simplify using `only [B, h, ↓reduceIte, zero_add]`.

Conclude with `LeftDerivativeCurves.good_LZ hD (hW l).1 (hW l).2`. Establish `hcong : ∀ {T T' S S' : (Mx k r → E) → Mx k r → E}, LeftDerivativeCurves.Comm k r i D T S → (∀ f x, T f x = T' f x) → (∀ f x, S f x = S' f x) → LeftDerivativeCurves.Comm k r i D T' S'`. Introduce `T T' S S' h e1 e2`. Establish `h1 : T' = T` using `funext fun f => funext fun x => (e1 f x).symm`. Establish `h2 : S' = S` using `funext fun f => funext fun x => (e2 f x).symm`.

Substitute `h1 h2` using the available equality. Conclude with `h`. Establish `hcomm : ∀ l l', LeftDerivativeCurves.Comm k r i D (B l') (A l)`. Introduce `l l'`. Use `hcong (LeftDerivativeCurves.comm_lop_rop hD (hW l').1 (hW l').2 (hZ l).1 (hZ l).2 (if ps l' then cs l' else 0) (if ps l then cs l else 0)) (fun f x => ?_) (fun f x => ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases h : ps l' <;> simp [LeftDerivativeCurves.lop, B, h, add_comm]`. Apply the tactic sequence `by_cases h : ps l <;> simp [LeftDerivativeCurves.rop, A, h, add_comm]`. Establish `hpt : ∀ l, ∀ f, A l f g₀ = B l f g₀`. Introduce `l f`. Simplify using `only [A, B, Pi.add_apply, hconj l, LeftDerivativeCurves.RZ_conj hgU]`.

Establish `h` using `LeftDerivativeCurves.swap_list hg₀ (List.ofFn fun l => (A l, B l)) (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hAg l) (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hBg l) (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hpt l) (fun p hp …`. Take `⟨l, rfl⟩` from `List.mem_ofFn.1 hp`. Take `⟨l', rfl⟩` from `List.mem_ofFn.1 hq`. Conclude with `hcomm l l') f hf`. Rewrite `h` using `[List.map_ofFn, List.map_ofFn]`.

Conclude with `h`.
-/
private theorem swap_lemma_4 {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
    {D : Set (Mx k r)} (hD : IsOpen D) {g₀ : Mx k r} (hg₀ : g₀ ∈ Glev k r i ∩ D) (n : ℕ)
    (ps : Fin n → Prop) [∀ l, Decidable (ps l)] (cs : Fin n → ℂ) (Zs Ws : Fin n → Mx k r)
    (hW : ∀ l, inLieLev k r i (hpart1 (Hpk k r) (Ws l)) ∧ inLieLev k r i (hpart2 (Hpk k r) (Ws l)))
    (hconj : ∀ l, Zs l = g₀⁻¹ * Ws l * g₀) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    (List.ofFn fun l => fun y : Mx k r → E => (if ps l then cs l • y else 0) + RZ (Hpk k r) (Zs l) y).foldr
        (fun T h => T h) f g₀ =
      (List.ofFn fun l => fun y : Mx k r → E => (if ps l then cs l • y else 0) + LZ (Hpk k r) (Ws l) y).foldl
        (fun h T => T h) f g₀ := by
  have hgU : g₀ ∈ UH (Hpk k r) := hg₀.1.1
  have hZ : ∀ l, inLieLev k r i (hpart1 (Hpk k r) (Zs l)) ∧ inLieLev k r i (hpart2 (Hpk k r) (Zs l)) := by
    intro l
    rw [hconj l, LeftDerivativeCurves.hpart1_conj hgU, LeftDerivativeCurves.hpart2_conj hgU]
    exact ⟨LeftDerivativeCurves.lie_conj hg₀.1 (hW l).1, LeftDerivativeCurves.lie_conj hg₀.1 (hW l).2⟩
  let A : Fin n → (Mx k r → E) → Mx k r → E := fun l y => (if ps l then cs l • y else 0) + RZ (Hpk k r) (Zs l) y
  let B : Fin n → (Mx k r → E) → Mx k r → E := fun l y => (if ps l then cs l • y else 0) + LZ (Hpk k r) (Ws l) y
  have hAg : ∀ l, Qx2.Good k r i D (A l) := by
    intro l
    by_cases h : ps l
    · simp only [A, h, ↓reduceIte]
      exact (Qx2.good_id.smul (cs l)).add (LeftDerivativeCurves.good_RZ hD (hZ l).1 (hZ l).2)
    · simp only [A, h, ↓reduceIte, zero_add]
      exact LeftDerivativeCurves.good_RZ hD (hZ l).1 (hZ l).2
  have hBg : ∀ l, Qx2.Good k r i D (B l) := by
    intro l
    by_cases h : ps l
    · simp only [B, h, ↓reduceIte]
      exact (Qx2.good_id.smul (cs l)).add (LeftDerivativeCurves.good_LZ hD (hW l).1 (hW l).2)
    · simp only [B, h, ↓reduceIte, zero_add]
      exact LeftDerivativeCurves.good_LZ hD (hW l).1 (hW l).2
  have hcong : ∀ {T T' S S' : (Mx k r → E) → Mx k r → E}, LeftDerivativeCurves.Comm k r i D T S → (∀ f x, T f x = T' f x) →
      (∀ f x, S f x = S' f x) → LeftDerivativeCurves.Comm k r i D T' S' := by
    intro T T' S S' h e1 e2
    have h1 : T' = T := funext fun f => funext fun x => (e1 f x).symm
    have h2 : S' = S := funext fun f => funext fun x => (e2 f x).symm
    subst h1 h2
    exact h
  have hcomm : ∀ l l', LeftDerivativeCurves.Comm k r i D (B l') (A l) := by
    intro l l'
    refine hcong (LeftDerivativeCurves.comm_lop_rop hD (hW l').1 (hW l').2 (hZ l).1 (hZ l).2 (if ps l' then cs l' else 0)
      (if ps l then cs l else 0)) (fun f x => ?_) (fun f x => ?_)
    · by_cases h : ps l' <;> simp [LeftDerivativeCurves.lop, B, h, add_comm]
    · by_cases h : ps l <;> simp [LeftDerivativeCurves.rop, A, h, add_comm]
  have hpt : ∀ l, ∀ f, A l f g₀ = B l f g₀ := by
    intro l f
    simp only [A, B, Pi.add_apply, hconj l, LeftDerivativeCurves.RZ_conj hgU]
  have h := LeftDerivativeCurves.swap_list hg₀ (List.ofFn fun l => (A l, B l))
    (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hAg l)
    (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hBg l)
    (fun p hp => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp; exact hpt l)
    (fun p hp q hq => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hp
      obtain ⟨l', rfl⟩ := List.mem_ofFn.1 hq
      exact hcomm l l') f hf
  rw [List.map_ofFn, List.map_ofFn] at h
  exact h

/- English proof (translation)
Establish `hw : ∀ q, herm (Hpk k r) (bvec q) (g⁻¹ *ᵥ Bs b) = ((star (Bs b) ᵥ* Hpk k r) ᵥ* g) q`. Introduce `q`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, unitary_inv_conjTranspose_hermitian hg, ← Matrix.vecMul_vecMul]`. Simplify using `[bvec]`.

Establish `hw0 : ∀ q, herm (Hpk k r) (bvec q) (Bs b) = (star (Bs b) ᵥ* Hpk k r) q`. Introduce `q`. Unfold `herm`. Rewrite using `[Matrix.dotProduct_mulVec]`. Simplify using `[bvec]`.

Use extensionality with `p q`. Use `set w := star (Bs b) ᵥ* Hpk k r with hwdef`. Simplify using `only [unitB, Matrix.of_apply, hw, hw0, Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem unitB_conj {m : ℕ} {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (a b : Fin m) :
    unitB (Hpk k r) (fun a => g⁻¹ *ᵥ Bs a) a b = g⁻¹ * unitB (Hpk k r) Bs a b * g := by
  have hw : ∀ q, herm (Hpk k r) (bvec q) (g⁻¹ *ᵥ Bs b) = ((star (Bs b) ᵥ* Hpk k r) ᵥ* g) q := by
    intro q
    unfold herm
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, unitary_inv_conjTranspose_hermitian hg, ← Matrix.vecMul_vecMul]
    simp [bvec]
  have hw0 : ∀ q, herm (Hpk k r) (bvec q) (Bs b) = (star (Bs b) ᵥ* Hpk k r) q := by
    intro q
    unfold herm
    rw [Matrix.dotProduct_mulVec]
    simp [bvec]
  ext p q
  set w := star (Bs b) ᵥ* Hpk k r with hwdef
  simp only [unitB, Matrix.of_apply, hw, hw0, Matrix.mul_apply]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Conj

end LeftDerivativeCurves

open LeftDerivativeCurves in
/- English proof (translation)
Introduce `E _ _ k r m i D hD Bs hB w F hF g₀ hg₀`. Establish `hgU : g₀ ∈ UH (Hpk k r)` using `hg₀.1.1`. Establish `hL : ∀ a b, inLieLev k r i (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧ inLieLev k r i (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b))` using `fun a b => LeftDerivativeCurves.inLieLev_herm_components_of_mulVec_bvec_eq_zero (LeftDerivativeCurves.unitB_mulVec_bvec_eq_zero_of_not_inV Bs hB a b)`. Simplify using `only [capR, capLft, qmF, qmFrev, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Conclude with `LeftDerivativeCurves.swap_lemma_4 hD hg₀ m _ _ (fun l => unitB (Hpk k r) (fun a => g₀⁻¹ *ᵥ Bs a) (id (σ l)) (id l)) (fun l => unitB (Hpk k r) Bs (id (σ l)) (id l)) (fun l => hL _ _) (fun l => unitB_conj hgU Bs _ _) F hF`.
-/
theorem left_right_swap : Formalism.FourierDecayAlt.Qr.LeftRightSwap := by
  intro E _ _ k r m i D hD Bs hB w F hF g₀ hg₀
  have hgU : g₀ ∈ UH (Hpk k r) := hg₀.1.1
  have hL : ∀ a b, inLieLev k r i (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieLev k r i (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) :=
    fun a b => LeftDerivativeCurves.inLieLev_herm_components_of_mulVec_bvec_eq_zero (LeftDerivativeCurves.unitB_mulVec_bvec_eq_zero_of_not_inV Bs hB a b)
  simp only [capR, capLft, qmF, qmFrev, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact LeftDerivativeCurves.swap_lemma_4 hD hg₀ m _ _ (fun l => unitB (Hpk k r) (fun a => g₀⁻¹ *ᵥ Bs a) (id (σ l)) (id l))
    (fun l => unitB (Hpk k r) Bs (id (σ l)) (id l)) (fun l => hL _ _) (fun l => unitB_conj hgU Bs _ _) F hF

end Formalism.FourierDecayAlt.P
