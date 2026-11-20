import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

/- English proof (translation)
The claim follows from `integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)`.
-/
theorem integrable_of_continuous' {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

/- English proof (translation)
Establish `e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ)`. Use function extensionality and compare the values at `k`. Conclude with `Complex.mul_conj (φ k)`. Rewrite `h` using `[e, integral_complex_ofReal, Complex.ofReal_eq_zero]`. Establish `hcs : Continuous fun k => Complex.normSq (φ k)` using `Complex.continuous_normSq.comp hc`.

Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k)) (integrable_of_continuous' hcs)).1 h`. Establish `h2 : (fun k => Complex.normSq (φ k)) = 0` using `(Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae`. Use function extensionality and compare the values at `k`. Use `congrFun h2 k` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_integral_mul_star {ε : Fin n → Bool} {φ : KG ε → ℂ} (hc : Continuous φ)
    (h : ∫ k, φ k * star (φ k) ∂(muK ε) = 0) : φ = 0 := by
  have e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ) := by
    funext k; exact Complex.mul_conj (φ k)
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hcs : Continuous fun k => Complex.normSq (φ k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k))
    (integrable_of_continuous' hcs)).1 h
  have h2 : (fun k => Complex.normSq (φ k)) = 0 := (Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae
  funext k
  have := congrFun h2 k
  simpa using this

/- English proof (translation)
Establish `hlow : lowV ε i ≤ polyV ε i`. Consider the cases of `i with`. Consider the case `zero => simp [lowV]`. Consider the case `succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)`. Set `W : Submodule ℂ (KG ε → ℂ)` to `{ carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0} add_mem' := by`.

Introduce and unpack `a b ⟨ha, ha'⟩ ⟨hb, hb'⟩`. Use `⟨add_mem ha hb, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hq'` using `continuous_of_mem (hlow hq)`. Establish `h1` using `integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k) (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha))) (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))`. Simplify using `only [Pi.add_apply, mul_add]`.

Rewrite using `[h1, ha' q hq, hb' q hq, add_zero]`. Use the proof step `zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨ha, ha'⟩`. Use `⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]`. Rewrite using `[integral_const_mul, ha' q hq, mul_zero] }`. Establish `hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0` using `fun p => Iff.rfl`. Set `B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i)` to `LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε)) (fun e e' p => by`. Establish `h1` using `integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k) (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k) (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2))) (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuou …`.

Simplify using `only [Submodule.coe_add, Pi.add_apply, add_mul]`. Conclude with `h1)`. Use the proof step `(fun c e p => by`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul c _)`.

Use the proof step `(fun e p p' => by`. Establish `h1` using `integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k) (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k) (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2))) (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous …`. Simplify using `only [Submodule.coe_add, Pi.add_apply, mul_add]`. Conclude with `h1)`. Use the proof step `(fun c e p => by`.

Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]`. Conclude with `integral_const_mul c _)`. Establish `hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective B`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `e he`. Establish `h0` using `hB e ⟨_, star_mem e.2⟩`. Rewrite `h0` using `[he]`. Establish `hz : (e : KG ε → ℂ) = 0` using `eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm`. Conclude with `Subtype.ext hz`.

Establish `hsurj : Function.Surjective B` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj`. Set `f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i` to `(lowV ε i).mkQ ∘ₗ W.subtype`. Establish `hker : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `w hw`.

Establish `hwl : (w : KG ε → ℂ) ∈ lowV ε i` using `(Submodule.Quotient.mk_eq_zero _).1 hw`. Establish `h0` using `((hW w).1 w.2).2 _ hwl`. Establish `hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) = fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k)` using `funext fun k => mul_comm _ _`. Rewrite `h0` using `[hc]`. Conclude with `Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)`.

Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective f hker`. Set `g : (KG ε → ℂ) →ₗ[ℂ] ℂ` to `(LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ`. Establish `hgW : ∀ w ∈ W, g w = w 1`. Introduce `w hw`. Use `LinearMap.congr_fun hr ⟨w, hw⟩` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this`. Simplify using `only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]`. Establish `hgU : ∀ q ∈ lowV ε i, g q = 0`. Introduce `q hq`. Simplify using `only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero, LinearMap.proj_apply]`.

Take `⟨e, he⟩` from `hsurj (g ∘ₗ (polyV ε i).subtype)`. Use `⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun he ⟨q, hlow hq⟩` as an intermediate fact. Rewrite `this` using `[hB]`. Rewrite using `[this]`.

Conclude with `hgU q hq`. Use `LinearMap.congr_fun he ⟨p, hp⟩` as an intermediate fact. Rewrite `this` using `[hB]`. Rewrite using `[this]`. Conclude with `hgW p ⟨hp, hpo⟩`.
-/
theorem exists_isKer (ε : Fin n → Bool) (i : ℕ) : ∃ e, IsKer ε i e := by
  classical
  have hlow : lowV ε i ≤ polyV ε i := by
    cases i with
    | zero => simp [lowV]
    | succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)
  let W : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun q hq => ?_⟩
        have hq' := continuous_of_mem (hlow hq)
        have h1 := integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k)
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha)))
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))
        simp only [Pi.add_apply, mul_add]
        rw [h1, ha' q hq, hb' q hq, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ha' q hq, mul_zero] }
  have hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0 :=
    fun p => Iff.rfl

  let B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i) :=
    LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε))
      (fun e e' p => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuous_of_mem p.2)))
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e p p' => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p'.2)))
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro e he
    have h0 := hB e ⟨_, star_mem e.2⟩
    rw [he] at h0
    have hz : (e : KG ε → ℂ) = 0 := eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm
    exact Subtype.ext hz
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj

  let f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i := (lowV ε i).mkQ ∘ₗ W.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwl : (w : KG ε → ℂ) ∈ lowV ε i := (Submodule.Quotient.mk_eq_zero _).1 hw
    have h0 := ((hW w).1 w.2).2 _ hwl
    have hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) =
        fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k) := funext fun k => mul_comm _ _
    rw [hc] at h0
    exact Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let g : (KG ε → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ
  have hgW : ∀ w ∈ W, g w = w 1 := by
    intro w hw
    have := LinearMap.congr_fun hr ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]
  have hgU : ∀ q ∈ lowV ε i, g q = 0 := by
    intro q hq
    simp only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero,
      LinearMap.proj_apply]
  obtain ⟨e, he⟩ := hsurj (g ∘ₗ (polyV ε i).subtype)
  refine ⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩
  · have := LinearMap.congr_fun he ⟨q, hlow hq⟩
    rw [hB] at this
    rw [this]
    exact hgU q hq
  · have := LinearMap.congr_fun he ⟨p, hp⟩
    rw [hB] at this
    rw [this]
    exact hgW p ⟨hp, hpo⟩

end GlobalTheory.KFourier
