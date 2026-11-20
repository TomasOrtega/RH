import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharApplyEqAdelicCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPairStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open scoped FourierTransform

noncomputable section
namespace GlobalTheory.ThetaRatSum
open MeasureTheory GroundTheory.Automorphic.GJMatrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
The claim follows from `GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar F ψ hψ x`.
-/
theorem char_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : AF F) :
    ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar F ψ hψ x

/- English proof (translation)
The claim follows from `GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar F κ`.
-/
theorem glue_integral : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ H : (κ → AF F) → ℂ,
    (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
    ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar F κ

/- English proof (translation)
The claim follows from `GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem F κ φ hφ u`.
-/
theorem shift_mem {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem F κ φ hφ u

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, g, hg, rfl⟩`. Establish `e : pureA F f g = schwartzBruhatTensorPi f g` using `rfl`. Rewrite using `[e]`. Conclude with `schwartzBruhatTensorPi_mem f ((mem_finiteSchwartzBruhatPi F).2 ⟨hg.1, hg.2⟩)`.
-/
theorem schA_le (ι : Type) [Fintype ι] : schA F ι ≤ schwartzBruhatPi F ι := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have e : pureA F f g = schwartzBruhatTensorPi f g := rfl
  rw [e]
  exact schwartzBruhatTensorPi_mem f ((mem_finiteSchwartzBruhatPi F).2 ⟨hg.1, hg.2⟩)

/- English proof (translation)
The claim follows from `GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs F κ φ hφ`.
-/
theorem summable_four {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F
      (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))
      (fun i => algebraMap F (AF F) (uv.2 i))‖ := GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs F κ φ hφ

abbrev rv (u : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (u i)

/- English proof (translation)
Simplify using `[dotProduct, Fintype.sum_sum_type]`.
-/
theorem dot_elim_left (a b : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim b 0 = ∑ i, a i * b i := by
  simp [dotProduct, Fintype.sum_sum_type]

/- English proof (translation)
Simplify using `[dotProduct, Fintype.sum_sum_type, rv, map_sum, map_mul]`.
-/
theorem dot_elim_rat (u v : κ → F) :
    Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F) = algebraMap F (AF F) (u ⬝ᵥ v) := by
  simp [dotProduct, Fintype.sum_sum_type, rv, map_sum, map_mul]

/- English proof (translation)
Use `set H : (κ → AF F) → ℂ := fun t => φ (Sum.elim (t + rv u) t) * (GroundTheory.Global.adelicChar F (∑ i, t i * rv v i) : ℂ) with hH`. Establish `hint : Integrable H (adeleMeasurePi F)` using `integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi (shift_mem hφ _)) _`. Establish `key : GlobalTheory.DiagForm.resD F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) = fun p => H (GlobalTheory.DiagForm.glue p)`. Use function extensionality and compare the values at `p`. Use `show ψ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) ⬝ᵥ Sum.elim (rv v) 0 + ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) 0)) * φ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0) = _`.

Establish `h2 : ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F)) = algebraMap F (AF F) (⅟(2 : F) * (u ⬝ᵥ v))`. Rewrite using `[dot_elim_rat, map_mul]`. Use `congr 1`. Establish `h3 : Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0 = Sum.elim (GlobalTheory.DiagForm.glue p + rv u) (GlobalTheory.DiagForm.glue p)`. Apply the tactic sequence `funext i; cases i <;> simp`.

Rewrite using `[dot_elim_left, h2, AddChar.map_add_eq_mul, hψ.2.1, mul_one, h3, char_eq ψ hψ, hH, mul_comm]`. Rewrite using `[GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, key, GlobalTheory.DiagForm.Lext_apply _ (((hB H).1).2 hint), (hB H).2, adelicFourierPi]`.
-/
theorem term_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {c₀ : ℝ}
    (hB : ∀ H : (κ → AF F) → ℂ,
      (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F))
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u v : κ → F) :
    GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      c₀ * adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + rv u) t)) (rv v) := by
  set H : (κ → AF F) → ℂ := fun t => φ (Sum.elim (t + rv u) t) *
    (GroundTheory.Global.adelicChar F (∑ i, t i * rv v i) : ℂ) with hH
  have hint : Integrable H (adeleMeasurePi F) :=
    integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi (shift_mem hφ _)) _
  have key : GlobalTheory.DiagForm.resD F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      fun p => H (GlobalTheory.DiagForm.glue p) := by
    funext p
    show ψ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) ⬝ᵥ Sum.elim (rv v) 0 +
        ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) 0)) *
        φ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0) = _
    have h2 : ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F)) =
        algebraMap F (AF F) (⅟(2 : F) * (u ⬝ᵥ v)) := by
      rw [dot_elim_rat, map_mul]
      congr 1
    have h3 : Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0 =
        Sum.elim (GlobalTheory.DiagForm.glue p + rv u) (GlobalTheory.DiagForm.glue p) := by
      funext i; cases i <;> simp
    rw [dot_elim_left, h2, AddChar.map_add_eq_mul, hψ.2.1, mul_one, h3, char_eq ψ hψ, hH, mul_comm]
  rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, key,
    GlobalTheory.DiagForm.Lext_apply _ (((hB H).1).2 hint), (hB H).2, adelicFourierPi]

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _`. Take `⟨c₀, hc₀, hB⟩` from `glue_integral (F := F) (κ := κ)`. Use `⟨(c₀ : ℂ), by exact_mod_cast hc₀.ne', fun φ hφ => ?_⟩` and prove the remaining obligations. Use `set f : (κ → F) → (κ → AF F) → ℂ := fun u t => φ (Sum.elim (t + rv u) t) with hf`. Establish `hT : (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) = fun uv => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2)`.

Use function extensionality and compare the values at `fun uv => term_eq ψ hψ hB hφ uv.1 uv.2`. Rewrite using `[hT]`. Establish `hs : Summable fun uv : (κ → F) × (κ → F) => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2)` using `(summable_four hφ).of_norm.mul_left _`. Establish `hP : ∀ u : κ → F, HasSum (fun v => (c₀ : ℂ) * adelicFourierPi F (f u) (rv v)) ((c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η)))`. Introduce `u`.

Take `⟨-, h2, h3⟩` from `poisson_of_mem_schwartzBruhatPi (shift_mem hφ (rv u))`. Use `HasSum.mul_left _ ?_` and prove the remaining obligations. Establish `e` using `h2.of_norm.hasSum`. Rewrite `e` using `[← h3]`. Conclude with `e`.

Establish `hθ : HasSum (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) (thetaSum F φ)`. Apply the tactic sequence `let e : (κ → F) × (κ → F) ≃ (κ ⊕ κ → F) := { toFun := fun uη => Sum.elim (uη.2 + uη.1) uη.2 invFun := fun ξ => (ξ ∘ Sum.inl - ξ ∘ Sum.inr, ξ ∘ Sum.inr) left_inv := fun uη => by ext i <;> simp right_inv := fun ξ => by funext i; cases i <;> simp }`. Take `⟨h1, -, -⟩` from `poisson_of_mem_schwartzBruhatPi (schA_le (F := F) (κ ⊕ κ) hφ)`. Establish `h` using `h1.of_norm.hasSum`. Rewrite `h` using `[← e.hasSum_iff]`.

Establish `hfe : (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) = (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i)) ∘ e`. Use function extensionality and compare the values at `uη`. Simplify using `only [Function.comp_apply]`. Use `congr 1`. Apply the tactic sequence `funext i; cases i <;> simp [e, rv, map_add]`.

Rewrite using `[hfe]`. Conclude with `h`. Establish `h4 : HasSum (fun u : κ → F => (c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η))) ((c₀ : ℂ) * thetaSum F φ)` using `(hθ.prod_fiberwise fun u => (hθ.summable.prod_factor u).hasSum).mul_left _`. Establish `h5` using `hs.hasSum.prod_fiberwise hP`. Rewrite using `[← h5.unique h4]`.

Conclude with `hs.hasSum`.
-/
theorem hasSum_lDiag_schr_rat : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F (κ ⊕ κ),
      HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ))
        (c * thetaSum F φ) := by
  intro F _ _ ψ hψ κ _
  obtain ⟨c₀, hc₀, hB⟩ := glue_integral (F := F) (κ := κ)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hc₀.ne', fun φ hφ => ?_⟩
  set f : (κ → F) → (κ → AF F) → ℂ := fun u t => φ (Sum.elim (t + rv u) t) with hf
  have hT : (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) =
      fun uv => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    funext fun uv => term_eq ψ hψ hB hφ uv.1 uv.2
  rw [hT]
  have hs : Summable fun uv : (κ → F) × (κ → F) => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    (summable_four hφ).of_norm.mul_left _
  have hP : ∀ u : κ → F, HasSum (fun v => (c₀ : ℂ) * adelicFourierPi F (f u) (rv v))
      ((c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η))) := by
    intro u
    obtain ⟨-, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (shift_mem hφ (rv u))
    refine HasSum.mul_left _ ?_
    have e := h2.of_norm.hasSum
    rw [← h3] at e
    exact e
  have hθ : HasSum (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) (thetaSum F φ) := by
    let e : (κ → F) × (κ → F) ≃ (κ ⊕ κ → F) :=
      { toFun := fun uη => Sum.elim (uη.2 + uη.1) uη.2
        invFun := fun ξ => (ξ ∘ Sum.inl - ξ ∘ Sum.inr, ξ ∘ Sum.inr)
        left_inv := fun uη => by ext i <;> simp
        right_inv := fun ξ => by funext i; cases i <;> simp }
    obtain ⟨h1, -, -⟩ := poisson_of_mem_schwartzBruhatPi (schA_le (F := F) (κ ⊕ κ) hφ)
    have h := h1.of_norm.hasSum
    rw [← e.hasSum_iff] at h
    have hfe : (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) =
        (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i)) ∘ e := by
      funext uη
      simp only [Function.comp_apply]
      congr 1
      funext i; cases i <;> simp [e, rv, map_add]
    rw [hfe]
    exact h
  have h4 : HasSum (fun u : κ → F => (c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η)))
      ((c₀ : ℂ) * thetaSum F φ) :=
    (hθ.prod_fiberwise fun u => (hθ.summable.prod_factor u).hasSum).mul_left _
  have h5 := hs.hasSum.prod_fiberwise hP
  rw [← h5.unique h4]
  exact hs.hasSum

end GlobalTheory.ThetaRatSum
