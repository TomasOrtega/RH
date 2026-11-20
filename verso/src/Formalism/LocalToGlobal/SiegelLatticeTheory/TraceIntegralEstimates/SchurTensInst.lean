import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensDense

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs Formalism.MainNotions.S

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, hnorm, hcont⟩` from `hU`. Establish `hmem : ∀ g : Formalism.REAL.UJ ε, uMat g ∈ UJset ε` using `fun g => g.2`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show σ (uMat 1) = 1`. Simplify `h1` using `[uMat]`.

Introduce `x y show σ (uMat (x * y)) = σ (uMat x) * σ (uMat y)`. Rewrite using `[show uMat (x * y) = uMat x * uMat y from rfl, hmul _ (hmem x) _ (hmem y)]`. Both sides reduce to the same expression. Introduce `x a b`. Set `Li : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (σ (uMat x)).toLinearMap, norm_map' := hnorm _ (hmem x) }`.

Conclude with `Li.inner_map_map a b`. Introduce `a`. Conclude with `(hcont a).comp_continuous (Units.continuous_val.comp continuous_subtype_val) hmem`.
-/
theorem unitRep_of_URepOn {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) :
    IsUnitRep (fun g : Formalism.REAL.UJ ε => σ (uMat g)) := by
  obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hU
  have hmem : ∀ g : Formalism.REAL.UJ ε, uMat g ∈ UJset ε := fun g => g.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show σ (uMat 1) = 1
    simpa [uMat] using h1
  · intro x y
    show σ (uMat (x * y)) = σ (uMat x) * σ (uMat y)
    rw [show uMat (x * y) = uMat x * uMat y from rfl, hmul _ (hmem x) _ (hmem y)]
    rfl
  · intro x a b
    let Li : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat x)).toLinearMap, norm_map' := hnorm _ (hmem x) }
    exact Li.inner_map_map a b
  · intro a
    exact (hcont a).comp_continuous (Units.continuous_val.comp continuous_subtype_val) hmem

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun a b a' b' => h.2 a b a' b'⟩`.
-/
theorem isSchur_of_isFdeg {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg (Formalism.REAL.muG ε) σ d) : IsSchur (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (uMat g)) d :=
  ⟨h.1, fun a b a' b' => h.2 a b a' b'⟩

/- English proof (translation)
Take `⟨hd, hI⟩` from `h`. Establish `h2` using `(hI w w w w).2`. Establish `hc : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ)` using `fun g => by`. Rewrite using `[Complex.star_def]`. Rewrite using `[RCLike.mul_conj (K := ℂ)]`.

Use `norm_cast`. Establish `hin : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`. Simplify using `only [hc] at h2`.

Rewrite `h2` using `[integral_complex_ofReal, hin]`. Establish `hr : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)) = ‖w‖ ^ 4 / d`. Establish `h3 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ)`. Rewrite using `[h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions. Establish `hw' : ‖w‖ ≠ 0` using `norm_ne_zero_iff.mpr hw`. Establish `hd' : d ≠ 0` using `hd.ne'`. Unfold `fdegOf`.

Rewrite using `[hr]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegOf_eq' {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d)
    {w : H} (hw : w ≠ 0) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, hI⟩ := h
  have h2 := (hI w w w w).2
  have hc : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def]
    rw [RCLike.mul_conj (K := ℂ)]
    norm_cast
  have hin : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hc] at h2
  rw [integral_complex_ofReal, hin] at h2
  have hr : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)) = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [h2]
      push_cast
      ring
    exact_mod_cast h3
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hd' : d ≠ 0 := hd.ne'
  unfold fdegOf
  rw [hr]
  field_simp

end Loc

/- English proof (translation)
Introduce `D X`. Establish `hU : ∀ v, IsUnitRep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g))` using `fun v => unitRep_of_URepOn (X.ds v).2.2.1`. Establish `hw : ∀ v, ‖X.B.w v‖ = 1` using `fun v => (X.low v).1`. Establish `hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v)`. Introduce `v`.

Take `⟨d, hd⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ (X.B.σ v) (X.ds v)`. Establish `hw0 : X.B.w v ≠ 0`. Introduce `h0`. Use `hw v` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `he : X.dv v = d` using `fdegOf_eq' hd hw0`. Rewrite using `[he]`. Conclude with `hd`. Establish `hT : IsTensAbs (fun v (g : Formalism.REAL.UJ (X.B.I.ε v)) => X.B.σ v (uMat g)) X.B.σs X.B.tens` using `X.B.tens_spec`.

Use `⟨isUnitRep_tens hU hT, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isSchur_tens (fun v => Formalism.REAL.muG (X.B.I.ε v)) X.dv hU (fun v => isSchur_of_isFdeg (hF v)) hT`. Establish `h1` using `X.B.tens_spec.1 X.B.w X.B.w`. Establish `h2 : ∏ v, ⟪X.B.w v, X.B.w v⟫_ℂ = 1`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_self_eq_norm_sq_to_K, hw v]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`. Establish `h3 : ‖X.B.tens X.B.w‖ ^ 2 = 1`. Use `congrArg RCLike.re h1` as an intermediate fact.

Rewrite `this` using `[inner_self_eq_norm_sq (𝕜 := ℂ)]`. Simplify using `using this`. Establish `h4` using `norm_nonneg (X.B.tens X.B.w)`. Use polynomial arithmetic with `[h3, h4]`. Introduce `y`.

Simplify using `only [Formalism.L2.SG.ProjRows.phInf, Formalism.L2.SG.ProjRows.mInf, Formalism.L2.SG.RealObj.degX]`. Rewrite using `[X.B.tens_spec.2.1 y, X.B.tens_spec.1]`. Both sides reduce to the same expression.
-/
theorem stepSchurG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSchurG := by
  intro D X
  have hU : ∀ v, IsUnitRep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g)) := fun v =>
    unitRep_of_URepOn (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v) := by
    intro v
    obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ (X.B.σ v) (X.ds v)
    have hw0 : X.B.w v ≠ 0 := by
      intro h0
      have := hw v
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have he : X.dv v = d := fdegOf_eq' hd hw0
    rw [he]
    exact hd
  have hT : IsTensAbs (fun v (g : Formalism.REAL.UJ (X.B.I.ε v)) => X.B.σ v (uMat g)) X.B.σs X.B.tens :=
    X.B.tens_spec
  refine ⟨isUnitRep_tens hU hT, ?_, ?_, ?_⟩
  · exact isSchur_tens (fun v => Formalism.REAL.muG (X.B.I.ε v)) X.dv hU (fun v => isSchur_of_isFdeg (hF v)) hT
  · have h1 := X.B.tens_spec.1 X.B.w X.B.w
    have h2 : ∏ v, ⟪X.B.w v, X.B.w v⟫_ℂ = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hw v]
      simp
    rw [h2] at h1
    have h3 : ‖X.B.tens X.B.w‖ ^ 2 = 1 := by
      have := congrArg RCLike.re h1
      rw [inner_self_eq_norm_sq (𝕜 := ℂ)] at this
      simpa using this
    have h4 := norm_nonneg (X.B.tens X.B.w)
    nlinarith [h3, h4]
  · intro y
    simp only [Formalism.L2.SG.ProjRows.phInf, Formalism.L2.SG.ProjRows.mInf, Formalism.L2.SG.RealObj.degX]
    rw [X.B.tens_spec.2.1 y, X.B.tens_spec.1]
    rfl

end Formalism.L2.S.Pv.SchurTens
