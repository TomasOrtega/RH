import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.DerLinear

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

/- English proof (translation)
Establish `: CompleteSpace 𝔸` using `FiniteDimensional.complete ℝ 𝔸`. Set `_ : NormedAlgebra ℚ 𝔸` to `NormedAlgebra.restrictScalars ℚ ℝ 𝔸`. Set `f : 𝔸 →+* 𝔸ᵐᵒᵖ` to `{ toFun := fun b => MulOpposite.op (σ b) map_one' := by simp [H.one] map_mul' := fun b c => by simp [H.anti] map_zero' := by simp map_add' := fun b c => by simp }`. Establish `hf : Continuous f` using `MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)`. Establish `h` using `NormedSpace.map_exp f hf a`.

Apply `MulOpposite.op_injective` to reduce the goal to its premises. Rewrite using `[← NormedSpace.exp_op]`. Conclude with `h`.
-/
theorem anti_exp (H : IsLieData σ j s) (a : 𝔸) : σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let f : 𝔸 →+* 𝔸ᵐᵒᵖ :=
    { toFun := fun b => MulOpposite.op (σ b)
      map_one' := by simp [H.one]
      map_mul' := fun b c => by simp [H.anti]
      map_zero' := by simp
      map_add' := fun b c => by simp }
  have hf : Continuous f := MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)
  have h := NormedSpace.map_exp f hf a
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact h

/- English proof (translation)
Establish `: CompleteSpace 𝔸` using `FiniteDimensional.complete ℝ 𝔸`. Set `_ : NormedAlgebra ℚ 𝔸` to `NormedAlgebra.restrictScalars ℚ ℝ 𝔸`. Establish `hs : σ (j X) = -j X` using `(H.skew (j X)).2 ⟨X, rfl⟩`. Rewrite using `[anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel, NormedSpace.exp_zero]`.
-/
theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hs : σ (j X) = -j X := (H.skew (j X)).2 ⟨X, rfl⟩
  rw [anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel,
    NormedSpace.exp_zero]

/- English proof (translation)
Establish `: FiniteDimensional ℝ L` using `Module.Finite.of_injective j H.inj`. Establish `: CompleteSpace 𝔸` using `FiniteDimensional.complete ℝ 𝔸`. Establish `hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸)` using `contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt`. Conclude with `hexp.comp (LinearMap.toContinuousLinearMap j).contDiff`.
-/
theorem contDiff_exp (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by
  have : FiniteDimensional ℝ L := Module.Finite.of_injective j H.inj
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact hexp.comp (LinearMap.toContinuousLinearMap j).contDiff

omit [FiniteDimensional ℝ 𝔸] in
/- English proof (translation)
Establish `hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0` using `((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0`. Establish `hd : HasDerivAt (fun t : ℝ => t • X) X 0`. Simplify using `using (hasDerivAt_id (0 : ℝ)).smul_const X`. Establish `hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X)`. Rewrite using `[zero_smul]`.

Conclude with `hF.hasFDerivAt`. Conclude with `(hF'.comp_hasDerivAt (0 : ℝ) hd).deriv`.
-/
theorem der_eq_fderiv {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by
  have hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0 :=
    ((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0
  have hd : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X) := by
    rw [zero_smul]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hd).deriv

/- English proof (translation)
Introduce `g`. Establish `hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1` using `exp_unitary H`. Set `c : L × ℝ → 𝔸` to `fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))`. Establish `hcd : ContDiff ℝ ∞ c` using `((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))`. Establish `hcu : ∀ p, σ (c p) * c p = 1`.

Introduce `p`. Simplify using `only [c]`. Rewrite using `[H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]`. Establish `hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0` using `fun g => (hφ g).contDiffAt`. Establish `hF` using `contDiff_family H hl hφ0 hcd hcu g`.

Establish `key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) = fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ))`. Introduce `Y`. Establish `h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t)))`. Use function extensionality and compare the values at `t`. Simplify using `only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]`.

Establish `hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0` using `(hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)`. Establish `hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p))) (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0)` using `((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt`. Use `show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _`. Rewrite using `[h1]`. Conclude with `(hFd.comp_hasDerivAt (0 : ℝ) hd).deriv`.

Repeatedly rewrite using `[key]`. Conclude with `(((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const`.
-/
theorem sm_der (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    Sm (expMap j s) (Der (expMap j s) X φ) := by
  intro g
  have hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1 := exp_unitary H
  let c : L × ℝ → 𝔸 := fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))
  have hcd : ContDiff ℝ ∞ c :=
    ((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hcu : ∀ p, σ (c p) * c p = 1 := by
    intro p
    simp only [c]
    rw [H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]
  have hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0 := fun g => (hφ g).contDiffAt
  have hF := contDiff_family H hl hφ0 hcd hcu g
  have key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) =
      fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ)) := by
    intro Y
    have h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t))) := by
      funext t
      simp only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]
    have hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)
    have hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p)))
        (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0) :=
      ((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt
    show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _
    rw [h1]
    exact (hFd.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp_rw [key]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

end GlobalTheory.SmoothForms.DerLinear

namespace GlobalTheory.SmoothForms

/- English proof (translation)
Introduce `𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ`. Use `⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Rewrite using `[Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add]`. Use function extensionality and compare the values at `g`.

Rewrite using `[Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul, smul_eq_mul]`.
-/
theorem der_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ
  refine ⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩
  · funext g
    rw [Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add]
  · funext g
    rw [Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul,
      smul_eq_mul]

end GlobalTheory.SmoothForms
