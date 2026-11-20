import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm

noncomputable section

open Filter Topology ContinuousAlternatingMap
open scoped ContDiff

namespace PositivityTheory.KB.TwAG

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}

/- English proof (translation)
Set `L1 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →L[ℝ] V)` to `LinearMap.toContinuousLinearMap.toLinearMap`. Set `L2 : (V →ₗ[ℝ] (V →L[ℝ] V)) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] V)` to `LinearMap.toContinuousLinearMap.toLinearMap`. Conclude with `⟨LinearMap.toContinuousLinearMap (L2 ∘ₗ f.compr₂ L1), fun a b c => rfl⟩`.
-/
theorem exists_clm (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) : ∃ B : V →L[ℝ] V →L[ℝ] V →L[ℝ] V, ∀ a b c, B a b c = f a b c := by
  let L1 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →L[ℝ] V) := LinearMap.toContinuousLinearMap.toLinearMap
  let L2 : (V →ₗ[ℝ] (V →L[ℝ] V)) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] V) := LinearMap.toContinuousLinearMap.toLinearMap
  exact ⟨LinearMap.toContinuousLinearMap (L2 ∘ₗ f.compr₂ L1), fun a b c => rfl⟩

/- English proof (translation)
Establish `hdiff : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => β.compContinuousLinearMap B)`. Set `M` to `ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℝ`. Use `haveI : FiniteDimensional ℝ M := Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ) : M →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin q => V) ℝ) ContinuousMultilinearMap.toMultilinearMap_injective`. Set `ι : (V [⋀^Fin q]→L[ℝ] ℝ) →ₗ[ℝ] M` to `(ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := ℝ) ℝ).toLinearMap`. Establish `hι : LinearMap.ker ι = ⊥` using `LinearMap.ker_eq_bot.2 ContinuousAlternatingMap.toContinuousMultilinearMap_injective`.

Take `⟨g, hg⟩` from `ι.exists_leftInverse_of_injective hι`. Set `G : M →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ)` to `⟨g, LinearMap.continuous_of_finiteDimensional g⟩`. Establish `key : (fun B : V →L[ℝ] V => β.compContinuousLinearMap B) = fun B => G (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B) β.toContinuousMultilinearMap)`. Use function extensionality and compare the values at `B`. Rewrite using `[ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]`.

Conclude with `(LinearMap.congr_fun hg (β.compContinuousLinearMap B)).symm`. Rewrite using `[key]`. Establish `hd : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => fun _ : Fin q => B)` using `contDiff_pi.2 fun _ => contDiff_id`. Establish `h1 : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B))` using `(ContinuousMultilinearMap.contDiff _).comp hd`. Establish `h2` using `(ContinuousLinearMap.apply ℝ M β.toContinuousMultilinearMap).contDiff.comp h1`.

Conclude with `G.contDiff.comp h2`. Conclude with `hdiff.contDiffAt.comp x hA`.
-/
theorem contDiffAt_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {α : X → V [⋀^Fin q]→L[ℝ] ℝ}
    {A : X → V →L[ℝ] V} {x : X} (β : V [⋀^Fin q]→L[ℝ] ℝ) (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (fun y => β.compContinuousLinearMap (A y)) x := by
  have hdiff : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => β.compContinuousLinearMap B) := by
    let M := ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℝ
    haveI : FiniteDimensional ℝ M := Module.Finite.of_injective
      (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ) :
        M →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin q => V) ℝ)
      ContinuousMultilinearMap.toMultilinearMap_injective
    let ι : (V [⋀^Fin q]→L[ℝ] ℝ) →ₗ[ℝ] M :=
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := ℝ) ℝ).toLinearMap
    have hι : LinearMap.ker ι = ⊥ :=
      LinearMap.ker_eq_bot.2 ContinuousAlternatingMap.toContinuousMultilinearMap_injective
    obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hι
    let G : M →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ) := ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
    have key : (fun B : V →L[ℝ] V => β.compContinuousLinearMap B) = fun B =>
        G (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B) β.toContinuousMultilinearMap) := by
      funext B
      rw [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
      exact (LinearMap.congr_fun hg (β.compContinuousLinearMap B)).symm
    rw [key]
    have hd : ContDiff ℝ ∞ (fun B : V →L[ℝ] V => fun _ : Fin q => B) :=
      contDiff_pi.2 fun _ => contDiff_id
    have h1 : ContDiff ℝ ∞ (fun B : V →L[ℝ] V =>
        ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin q => V) (fun _ : Fin q => V) ℝ (fun _ => B)) :=
      (ContinuousMultilinearMap.contDiff _).comp hd
    have h2 := (ContinuousLinearMap.apply ℝ M β.toContinuousMultilinearMap).contDiff.comp h1
    exact G.contDiff.comp h2
  exact hdiff.contDiffAt.comp x hA

/- English proof (translation)
Establish `hQ : ∀ x, HasFDerivAt (fun y => B y y) (B.flip x + B x) x`. Introduce `x`. Use `B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)` as an intermediate fact. Use `this.congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `w u`.

Simplify using `[add_comm]`. Establish `hQs : ContDiff ℝ ∞ (fun y => B y y)` using `B.contDiff.clm_apply contDiff_id`. Establish `hφs : ContDiff ℝ ∞ (fun y => B y y e)` using `hQs.clm_apply contDiff_const`. Set `L : V ≃L[ℝ] V` to `(LinearEquiv.smulOfNeZero ℝ V 2 two_ne_zero).toContinuousLinearEquiv`. Establish `hLw : ∀ w, (L : V →L[ℝ] V) w = (2 : ℝ) • w` using `fun w => rfl`.

Establish `hφe : HasFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e`. Establish `h0 : HasFDerivAt (fun y => B y y e) ((ContinuousLinearMap.apply ℝ V e).comp (B.flip e + B e)) e` using `(ContinuousLinearMap.apply ℝ V e).hasFDerivAt.comp e (hQ e)`. Use `h0 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `w`. Rewrite using `[hLw, ← he w]`.

Simplify using `[add_comm]`. Establish `hee : B e e e = e` using `by rw [h1]; rfl`. Establish `hstrict : HasStrictFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e` using `hφs.contDiffAt.hasStrictFDerivAt' hφe (by simp)`. Establish `hψ : ContDiffAt ℝ ∞ (hstrict.localInverse _ _ _) (B e e e)` using `hφs.contDiffAt.to_localInverse hφe (by simp)`. Establish `hright` using `hstrict.eventually_right_inverse`.

Establish `htend` using `hstrict.localInverse_tendsto`. Establish `himg` using `hstrict.localInverse_apply_image`. Rewrite `hright`, `htend`, `himg`, `hψ` using `[hee]`. Establish `hP : ContDiffAt ℝ ∞ (fun y => B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) e` using `hQs.contDiffAt.comp e hψ`. Establish `hPe : B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e) = 1`.

Rewrite using `[himg, h1]`. Establish `hunit : ∀ᶠ y in 𝓝 e, IsUnit (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))`. Establish `hm : {x : V →L[ℝ] V | IsUnit x} ∈ 𝓝 (B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e))` using `Units.isOpen.mem_nhds (by rw [hPe]; exact isUnit_one)`. Conclude with `hP.continuousAt.preimage_mem_nhds hm`. Establish `hid : ∀ᶠ y in 𝓝 e, (o y).compContinuousLinearMap (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) = o e` using `by filter_upwards [htend.eventually ho, hright] with y hy1 hy2`.

Rewrite `hy1` using `[hy2]`. Conclude with `hy1`. Establish `hrep : o =ᶠ[𝓝 e] fun y => (o e).compContinuousLinearMap (Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)))` using `by filter_upwards [hid, hunit] with y hy hu`. Rewrite using `[← hy]`. Use extensionality with `v`.

Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply]`. Rewrite using `[← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]`.

Both sides reduce to the same expression. Establish `hsm : ContDiffAt ℝ ∞ o e`. Establish `hR : ContDiffAt ℝ ∞ (fun y => Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))) e`. Use `ContDiffAt.comp (g := Ring.inverse) e ?_ hP` and prove the remaining obligations. Rewrite using `[hPe]`.

Simplify using `using contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) (1 : (V →L[ℝ] V)ˣ)`. Conclude with `(contDiffAt_comp (α := o) (o e) hR).congr_of_eventuallyEq hrep`. Use `⟨hsm, ?_⟩` and prove the remaining obligations. Establish `hdo : HasFDerivAt o (fderiv ℝ o e) e` using `(hsm.differentiableAt (by simp)).hasFDerivAt`. Establish `hG1 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x)) ((ContinuousAlternatingMap.compContinuousLinearMapCLM (B e e)) ∘L (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) + (o (B e e e)).fderivCompContinuousLinearMap (B e e) ∘L (B.flip e + B e)) e`.

Establish `h2 : HasFDerivAt (fun x => o (B x x e)) (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) e`. Establish `h3 : HasFDerivAt o (fderiv ℝ o e) (B e e e)` using `by rw [hee]; exact hdo`. Conclude with `HasFDerivAt.comp (g := o) (f := fun y => B y y e) e h3 hφe`. Conclude with `h2.continuousAlternatingMapCompContinuousLinearMap (hQ e)`. Establish `hG2 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x)) (0 : V →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ)) e` using `(hasFDerivAt_const (o e) e).congr_of_eventuallyEq ho`.

Establish `huniq` using `hG1.unique hG2`. Establish `hcomp1 : ∀ T : V [⋀^Fin q]→L[ℝ] ℝ, ContinuousAlternatingMap.compContinuousLinearMapCLM (1 : V →L[ℝ] V) T = T`. Introduce `T`. Use extensionality with `v`. Both sides reduce to the same expression.

Establish `hDw : ∀ w, fderiv ℝ o e w = (o e).fderivCompContinuousLinearMap 1 (((-(1/2 : ℝ)) • (B.flip e + B e)) w)`. Introduce `w`. Establish `hw` using `congrArg (fun T => T w) huniq`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hw`. Rewrite `hw` using `[hee, h1, hcomp1, hLw, map_smul]`.

Establish `hX` using `eq_neg_of_add_eq_zero_right hw`. Rewrite using `[ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.add_apply, hX, smul_neg, smul_smul]`. Apply the tactic sequence `first | norm_num | simp`. Establish `hfd : fderiv ℝ o e = (o e).fderivCompContinuousLinearMap 1 ∘L ((-(1/2 : ℝ)) • (B.flip e + B e))` using `by ext1 w`. Conclude with `hDw w`.

Rewrite using `[extDeriv, hfd]`. Apply `ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero` to reduce the goal to its premises. Introduce `x y`. Establish `hs` using `hsym x y`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]`.

Rewrite using `[add_comm (B x e y), hs, add_comm]`.
-/
theorem core (B : V →L[ℝ] V →L[ℝ] V →L[ℝ] V) (e : V) (h1 : B e e = 1)
    (hsym : ∀ x y, B e x y + B x e y = B e y x + B y e x) (he : ∀ y, B e y e + B y e e = (2 : ℝ) • y)
    (o : V → V [⋀^Fin q]→L[ℝ] ℝ) (ho : ∀ᶠ x in 𝓝 e, (o (B x x e)).compContinuousLinearMap (B x x) = o e) :
    ContDiffAt ℝ ∞ o e ∧ extDeriv o e = 0 := by
  have hQ : ∀ x, HasFDerivAt (fun y => B y y) (B.flip x + B x) x := by
    intro x
    have := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
    refine this.congr_fderiv ?_
    ext w u
    simp [add_comm]
  have hQs : ContDiff ℝ ∞ (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hφs : ContDiff ℝ ∞ (fun y => B y y e) := hQs.clm_apply contDiff_const
  let L : V ≃L[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V 2 two_ne_zero).toContinuousLinearEquiv
  have hLw : ∀ w, (L : V →L[ℝ] V) w = (2 : ℝ) • w := fun w => rfl
  have hφe : HasFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e := by
    have h0 : HasFDerivAt (fun y => B y y e) ((ContinuousLinearMap.apply ℝ V e).comp (B.flip e + B e)) e :=
      (ContinuousLinearMap.apply ℝ V e).hasFDerivAt.comp e (hQ e)
    convert h0 using 1
    ext w
    rw [hLw, ← he w]
    simp [add_comm]
  have hee : B e e e = e := by rw [h1]; rfl
  have hstrict : HasStrictFDerivAt (fun y => B y y e) (L : V →L[ℝ] V) e :=
    hφs.contDiffAt.hasStrictFDerivAt' hφe (by simp)
  have hψ : ContDiffAt ℝ ∞ (hstrict.localInverse _ _ _) (B e e e) :=
    hφs.contDiffAt.to_localInverse hφe (by simp)
  have hright := hstrict.eventually_right_inverse
  have htend := hstrict.localInverse_tendsto
  have himg := hstrict.localInverse_apply_image
  rw [hee] at hright htend himg hψ
  have hP : ContDiffAt ℝ ∞ (fun y => B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) e :=
    hQs.contDiffAt.comp e hψ
  have hPe : B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e) = 1 := by
    rw [himg, h1]
  have hunit : ∀ᶠ y in 𝓝 e, IsUnit (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) := by
    have hm : {x : V →L[ℝ] V | IsUnit x} ∈ 𝓝 (B (hstrict.localInverse _ _ _ e) (hstrict.localInverse _ _ _ e)) :=
      Units.isOpen.mem_nhds (by rw [hPe]; exact isUnit_one)
    exact hP.continuousAt.preimage_mem_nhds hm
  have hid : ∀ᶠ y in 𝓝 e, (o y).compContinuousLinearMap
      (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y)) = o e := by
    filter_upwards [htend.eventually ho, hright] with y hy1 hy2
    rw [hy2] at hy1
    exact hy1
  have hrep : o =ᶠ[𝓝 e] fun y => (o e).compContinuousLinearMap
      (Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))) := by
    filter_upwards [hid, hunit] with y hy hu
    rw [← hy]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]
    rfl
  have hsm : ContDiffAt ℝ ∞ o e := by
    have hR : ContDiffAt ℝ ∞
        (fun y => Ring.inverse (B (hstrict.localInverse _ _ _ y) (hstrict.localInverse _ _ _ y))) e := by
      refine ContDiffAt.comp (g := Ring.inverse) e ?_ hP
      rw [hPe]
      simpa using contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) (1 : (V →L[ℝ] V)ˣ)
    exact (contDiffAt_comp (α := o) (o e) hR).congr_of_eventuallyEq hrep
  refine ⟨hsm, ?_⟩
  have hdo : HasFDerivAt o (fderiv ℝ o e) e := (hsm.differentiableAt (by simp)).hasFDerivAt
  have hG1 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x))
      ((ContinuousAlternatingMap.compContinuousLinearMapCLM (B e e)) ∘L (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) +
        (o (B e e e)).fderivCompContinuousLinearMap (B e e) ∘L (B.flip e + B e)) e := by
    have h2 : HasFDerivAt (fun x => o (B x x e)) (fderiv ℝ o e ∘L (L : V →L[ℝ] V)) e := by
      have h3 : HasFDerivAt o (fderiv ℝ o e) (B e e e) := by rw [hee]; exact hdo
      exact HasFDerivAt.comp (g := o) (f := fun y => B y y e) e h3 hφe
    exact h2.continuousAlternatingMapCompContinuousLinearMap (hQ e)
  have hG2 : HasFDerivAt (fun x => (o (B x x e)).compContinuousLinearMap (B x x))
      (0 : V →L[ℝ] (V [⋀^Fin q]→L[ℝ] ℝ)) e :=
    (hasFDerivAt_const (o e) e).congr_of_eventuallyEq ho
  have huniq := hG1.unique hG2
  have hcomp1 : ∀ T : V [⋀^Fin q]→L[ℝ] ℝ,
      ContinuousAlternatingMap.compContinuousLinearMapCLM (1 : V →L[ℝ] V) T = T := by
    intro T
    ext v
    rfl
  have hDw : ∀ w, fderiv ℝ o e w = (o e).fderivCompContinuousLinearMap 1
      (((-(1/2 : ℝ)) • (B.flip e + B e)) w) := by
    intro w
    have hw := congrArg (fun T => T w) huniq
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hw
    rw [hee, h1, hcomp1, hLw, map_smul] at hw
    have hX := eq_neg_of_add_eq_zero_right hw
    rw [ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.add_apply, hX, smul_neg, smul_smul]
    first | norm_num | simp
  have hfd : fderiv ℝ o e = (o e).fderivCompContinuousLinearMap 1 ∘L
      ((-(1/2 : ℝ)) • (B.flip e + B e)) := by
    ext1 w
    exact hDw w
  rw [extDeriv, hfd]
  apply ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
  intro x y
  have hs := hsym x y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm (B x e y), hs, add_comm]

/- English proof (translation)
Establish `hfd : ∀ x, fderiv ℝ (⇑A) x = A` using `fun x => A.fderiv`. Establish `heq : (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) =ᶠ[𝓝 h] o` using `by filter_upwards [ho] with x hx`. Rewrite using `[hfd]`. Conclude with `hx`. Establish `hcA : ContDiffAt ℝ ∞ (fun x => o (A x)) h` using `hc.comp h A.contDiff.contDiffAt`.

Establish `hsm : ContDiffAt ℝ ∞ (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) h`. Simplify using `only [hfd]`. Conclude with `(ContinuousAlternatingMap.compContinuousLinearMapCLM A).contDiff.contDiffAt.comp h hcA`. Use `⟨hsm.congr_of_eventuallyEq heq.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← heq.extDeriv_eq, extDeriv_pullback (r := ∞) (hc.differentiableAt (by simp)) A.contDiff.contDiffAt (by simp; exact ENat.LEInfty.out), h0]`.

Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem transport (A : V →L[ℝ] V) {h : V} (o : V → V [⋀^Fin q]→L[ℝ] ℝ) (hc : ContDiffAt ℝ ∞ o (A h))
    (h0 : extDeriv o (A h) = 0) (ho : ∀ᶠ x in 𝓝 h, (o (A x)).compContinuousLinearMap A = o x) :
    ContDiffAt ℝ ∞ o h ∧ extDeriv o h = 0 := by
  have hfd : ∀ x, fderiv ℝ (⇑A) x = A := fun x => A.fderiv
  have heq : (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) =ᶠ[𝓝 h] o := by
    filter_upwards [ho] with x hx
    rw [hfd]
    exact hx
  have hcA : ContDiffAt ℝ ∞ (fun x => o (A x)) h := hc.comp h A.contDiff.contDiffAt
  have hsm : ContDiffAt ℝ ∞ (fun x => (o (A x)).compContinuousLinearMap (fderiv ℝ (⇑A) x)) h := by
    simp only [hfd]
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM A).contDiff.contDiffAt.comp h hcA
  refine ⟨hsm.congr_of_eventuallyEq heq.symm, ?_⟩
  rw [← heq.extDeriv_eq, extDeriv_pullback (r := ∞) (hc.differentiableAt (by simp))
    A.contDiff.contDiffAt
    (by simp; exact ENat.LEInfty.out), h0]
  ext v
  simp

end PositivityTheory.KB.TwAG

end
