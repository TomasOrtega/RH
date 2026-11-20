import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandGB

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GelfandGA

local notation "𝕄" => Fin n → Fin n → ℂ

def conjK (ε : Fin n → Bool) (k : KG ε) : 𝕄 →L[ℂ] 𝕄 := Ps1.conjCLM (toMK k⁻¹) (toMK k)

/- English proof (translation)
Rewrite using `[continuous_clm_apply]`. Introduce `y`. Establish `h1 : Continuous (fun k : KG ε => toMK k)`. Unfold `toMK`. Use `fun_prop`.

Establish `h2 : Continuous (fun k : KG ε => toMK k⁻¹)` using `h1.comp continuous_inv`. Use `show Continuous (fun k : KG ε => toMK k⁻¹ * (show Matrix (Fin n) (Fin n) ℂ from y) * toMK k)`. Conclude with `(h2.matrix_mul continuous_const).matrix_mul h1`.
-/
lemma continuous_conjK (ε : Fin n → Bool) : Continuous (conjK ε) := by
  rw [continuous_clm_apply]
  intro y
  have h1 : Continuous (fun k : KG ε => toMK k) := by
    unfold toMK
    fun_prop
  have h2 : Continuous (fun k : KG ε => toMK k⁻¹) := h1.comp continuous_inv
  show Continuous (fun k : KG ε => toMK k⁻¹ * (show Matrix (Fin n) (Fin n) ℂ from y) * toMK k)
  exact (h2.matrix_mul continuous_const).matrix_mul h1

def Lop {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : ℂ →L[ℂ] (T.V →L[ℂ] T.V) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip (T.op k * projW T * T.op k⁻¹)

/- English proof (translation)
Use `compactSpace_KG ε` as an intermediate fact. Establish `: IsFiniteMeasureOnCompacts (muK ε)` using `by unfold muK; infer_instance`. Establish `: IsFiniteMeasure (muK ε)` using `inferInstance`. Establish `hφ : ContDiffOn ℂ ∞ (Ps1.PhiP μ) (OmegaSet n : Set 𝕄)` using `fun z hz => (contDiffAt_phiM μ hz).contDiffWithinAt`. Establish `hL : Continuous (Lop T)` using `((ContinuousLinearMap.lsmul ℂ ℂ).flip).continuous.comp (Ps1.continuous_P T)`.

Establish `hU : IsOpen (Ps1.Uset ε : Set 𝕄)` using `Ps1.isOpen_Uset`. Establish `hΩ : IsOpen (OmegaSet n : Set 𝕄)` using `isOpen_omega`. Establish `h` using `GelfandGB.contDiffOn_param (muK ε) (conjK ε) (continuous_conjK ε) hU hΩ (fun x hx k => hx k) (Ps1.PhiP μ) (Lop T) hφ hL`. Establish `h' : ContDiffOn ℂ ∞ (fun x : 𝕄 => psM T μ x) (Ps1.Uset ε : Set 𝕄)` using `(h.const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).congr fun x _ => rfl`. Conclude with `h'`.
-/
theorem psM_contDiffOn {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ContDiffOn ℂ ∞ (psM T μ) (Ps1.Uset ε) := by
  have := compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hφ : ContDiffOn ℂ ∞ (Ps1.PhiP μ) (OmegaSet n : Set 𝕄) := fun z hz =>
    (contDiffAt_phiM μ hz).contDiffWithinAt
  have hL : Continuous (Lop T) :=
    ((ContinuousLinearMap.lsmul ℂ ℂ).flip).continuous.comp (Ps1.continuous_P T)
  have hU : IsOpen (Ps1.Uset ε : Set 𝕄) := Ps1.isOpen_Uset
  have hΩ : IsOpen (OmegaSet n : Set 𝕄) := isOpen_omega
  have h := GelfandGB.contDiffOn_param (muK ε) (conjK ε) (continuous_conjK ε) hU hΩ
    (fun x hx k => hx k) (Ps1.PhiP μ) (Lop T) hφ hL
  have h' : ContDiffOn ℂ ∞ (fun x : 𝕄 => psM T μ x) (Ps1.Uset ε : Set 𝕄) :=
    (h.const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).congr fun x _ => rfl
  exact h'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hlin : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z)`. Establish `h` using `(LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ X : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)).contDiff (n := ∞)`. Conclude with `h`. Unfold `Lhol`. Conclude with `((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2.clm_apply hlin.contDiffOn`.
-/
lemma lhol_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℂ ∞ (Lhol X F) U := by
  have hlin : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    have h := (LinearMap.toContinuousLinearMap
      (LinearMap.mulLeft ℂ X : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)).contDiff
      (n := ∞)
    exact h
  unfold Lhol
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2.clm_apply hlin.contDiffOn

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `a b`. Simplify using `only [opPow]`.

Use `split_ifs`. Conclude with `hF`. Conclude with `contDiffOn_const`. Consider the case `succ k ih`. Introduce `a b`.

Simplify using `only [opPow]`. Rewrite using `[Finset.sum_fn]`. Conclude with `ContDiffOn.sum fun c _ => lhol_contDiffOn hU (ih c b) (Y a c)`.
-/
lemma opPow_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {F : Matrix (Fin n) (Fin n) ℂ → E} (hF : ContDiffOn ℂ ∞ F U)
    (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∀ j a b, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (Y a b)) j a b F) U := by
  intro j
  induction j with
  | zero =>
    intro a b
    simp only [opPow]
    split_ifs
    · exact hF
    · exact contDiffOn_const
  | succ k ih =>
    intro a b
    simp only [opPow]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun c _ => lhol_contDiffOn hU (ih c b) (Y a c)

end GelfandGA

end ReciprocityTheory.ChartRestriction.DS.S7
