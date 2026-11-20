import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

namespace GlobalTheory.FockFamily

/- English proof (translation)
Introduce `hB hD hU`. Set `β₁ : V →ₗ[ℝ] (V →L[ℝ] ℝ)` to `(LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β`. Set `βc : V →L[ℝ] V →L[ℝ] ℝ` to `LinearMap.toContinuousLinearMap β₁`. Establish `hβc : ∀ x y, βc x y = β x y` using `fun x y => rfl`. Establish `hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ring.inverse (blockB (J t)))`.

Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t`. Conclude with `(contDiffAt_ringInverse ℝ (hU t).unit).comp t hB.contDiffAt`. Establish `hDC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (blockD (J t)).comp (Ring.inverse (blockB (J t))))` using `hD.clm_comp hC`. Establish `hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × V => (Real.pi : ℂ) * Complex.I)` using `contDiff_const`.

Establish `hπ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (Real.pi : ℂ) * Complex.I)` using `contDiff_const`. Establish `hR : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun e => ((f e : ℝ) : ℂ))` using `fun hf => Complex.ofRealCLM.contDiff.comp hf`. Prove the components needed by the constructor for the conclusion. Introduce `x y`. Establish `h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Real.pi * βc x (Ring.inverse (blockB (J t)) y))` using `contDiff_const.mul (contDiff_const.clm_apply (hC.clm_apply contDiff_const))`.

Establish `h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => βc x (((blockD (J t)).comp (Ring.inverse (blockB (J t)))) y))` using `contDiff_const.clm_apply (hDC.clm_apply contDiff_const)`. Use `(hR h1).add (hπ'.mul (hR h2))` as an intermediate fact. Simplify `this` using `only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply]`. Establish `hCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => Ring.inverse (blockB (J p.1)) p.2)` using `(hC.comp contDiff_fst).clm_apply contDiff_snd`. Establish `hDCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => ((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2)` using `(hDC.comp contDiff_fst).clm_apply contDiff_snd`.

Establish `hβp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2)` using `βc.contDiff.comp contDiff_snd`. Establish `h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => Real.pi * βc p.2 (Ring.inverse (blockB (J p.1)) p.2))` using `contDiff_const.mul (hβp.clm_apply hCp)`. Establish `h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2 (((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2))` using `hβp.clm_apply hDCp`. Use `(hR h1).add (hπ.mul (hR h2))` as an intermediate fact. Simplify `this` using `only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply]`.
-/
theorem fockForm_family_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  intro hB hD hU

  let β₁ : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β
  let βc : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap β₁
  have hβc : ∀ x y, βc x y = β x y := fun x y => rfl

  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ring.inverse (blockB (J t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (contDiffAt_ringInverse ℝ (hU t).unit).comp t hB.contDiffAt
  have hDC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => (blockD (J t)).comp (Ring.inverse (blockB (J t)))) := hD.clm_comp hC
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × V => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hπ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hR : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ},
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun e => ((f e : ℝ) : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  constructor
  · intro x y
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => Real.pi * βc x (Ring.inverse (blockB (J t)) y)) :=
      contDiff_const.mul (contDiff_const.clm_apply (hC.clm_apply contDiff_const))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => βc x (((blockD (J t)).comp (Ring.inverse (blockB (J t)))) y)) :=
      contDiff_const.clm_apply (hDC.clm_apply contDiff_const)
    have := (hR h1).add (hπ'.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this
  · have hCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Ring.inverse (blockB (J p.1)) p.2) :=
      (hC.comp contDiff_fst).clm_apply contDiff_snd
    have hDCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => ((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2) :=
      (hDC.comp contDiff_fst).clm_apply contDiff_snd
    have hβp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2) :=
      βc.contDiff.comp contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Real.pi * βc p.2 (Ring.inverse (blockB (J p.1)) p.2)) :=
      contDiff_const.mul (hβp.clm_apply hCp)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => βc p.2 (((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2)) :=
      hβp.clm_apply hDCp
    have := (hR h1).add (hπ.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this

end GlobalTheory.FockFamily
