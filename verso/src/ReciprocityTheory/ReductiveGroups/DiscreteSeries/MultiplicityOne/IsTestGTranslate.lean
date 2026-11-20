import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace Cut0Aux

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def lmulCLM (a : Mat k r) : Mat k r →L[ℝ] Mat k r where
  toFun y := a * y
  map_add' y y' := Matrix.mul_add a y y'
  map_smul' c y := Matrix.mul_smul a c y
  cont := continuous_const.matrix_mul continuous_id

/- English proof (translation)
Use `show Continuous fun x => a * Matrix.of x`. Conclude with `continuous_const.matrix_mul continuous_id`.
-/
theorem cont_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  show Continuous fun x => a * Matrix.of x
  exact continuous_const.matrix_mul continuous_id

def lmulME (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM (k := k) (r := r) a
  invFun := lmulM (k := k) (r := r) b
  left_inv x := by
    show b * (a * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
    rfl
  right_inv x := by
    show a * (b * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
    rfl
  measurable_toFun := (cont_lmulM a).measurable
  measurable_invFun := (cont_lmulM b).measurable

/- English proof (translation)
Take `⟨hsm, K, hK, hKv⟩` from `hφ`. Establish `hgi : g⁻¹ ∈ GV k r` using `WeylGroupFacts.uh_inv hg`. Establish `hdet` using `WeylGroupFacts.isUnit_of_uh hg`. Establish `hgg : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hdet`. Use `⟨fun g₀ hg₀ => ?_, (fun y => g * y) '' K, hK.image (continuous_const.matrix_mul continuous_id), fun y hy hyK => ?_⟩` and prove the remaining obligations.

Take `⟨U, f', hU, hgU, hf', hfe⟩` from `hsm (g⁻¹ * g₀) (WeylGroupFacts.uh_mul hgi hg₀)`. Use `⟨(fun y => g⁻¹ * y) ⁻¹' U, fun y => f' (g⁻¹ * y), hU.preimage (continuous_const.matrix_mul continuous_id), hgU, ?_, fun y hyU hyG => hfe _ hyU (WeylGroupFacts.uh_mul hgi hyG)⟩` and prove the remaining obligations. Conclude with `hf'.comp (lmulCLM g⁻¹).contDiff.contDiffOn (fun y hy => hy)`. Apply `hKv _ (WeylGroupFacts.uh_mul hgi hy)` to reduce the goal to its premises. Introduce `hK'`.

Apply `hyK` to reduce the goal to its premises. Use `⟨g⁻¹ * y, hK', ?_⟩` and prove the remaining obligations. Use `show g * (g⁻¹ * y) = y`. Rewrite using `[← Matrix.mul_assoc, hgg, Matrix.one_mul]`.
-/
theorem isTestG_translate {g : Mat k r} (hg : g ∈ GV k r) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    IsTestG (fun y => φ (g⁻¹ * y)) := by
  obtain ⟨hsm, K, hK, hKv⟩ := hφ
  have hgi : g⁻¹ ∈ GV k r := WeylGroupFacts.uh_inv hg
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  refine ⟨fun g₀ hg₀ => ?_, (fun y => g * y) '' K,
    hK.image (continuous_const.matrix_mul continuous_id), fun y hy hyK => ?_⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hsm (g⁻¹ * g₀) (WeylGroupFacts.uh_mul hgi hg₀)
    refine ⟨(fun y => g⁻¹ * y) ⁻¹' U, fun y => f' (g⁻¹ * y),
      hU.preimage (continuous_const.matrix_mul continuous_id), hgU, ?_,
      fun y hyU hyG => hfe _ hyU (WeylGroupFacts.uh_mul hgi hyG)⟩
    exact hf'.comp (lmulCLM g⁻¹).contDiff.contDiffOn (fun y hy => hy)
  · apply hKv _ (WeylGroupFacts.uh_mul hgi hy)
    intro hK'
    apply hyK
    refine ⟨g⁻¹ * y, hK', ?_⟩
    show g * (g⁻¹ * y) = y
    rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]

/- English proof (translation)
Establish `hdet` using `WeylGroupFacts.isUnit_of_uh hg`. Establish `hgg : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hdet`. Establish `hgg' : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hdet`. Set `e` to `lmulME (k := k) (r := r) g g⁻¹ hgg hgg'`. Establish `hmap : D.μG.map e = D.μG` using `D.haarG.left g hg`.

Establish `hconc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r` using `ae_iff.mpr D.haarG.conc`. Set `L : X.Hs →ₗᵢ[ℂ] X.Hs` to `{ toLinearMap := (X.σ g).toLinearMap, norm_map' := fun v => X.rep.2.1 g hg v }`. Establish `hL : ∀ v, L v = X.σ g v` using `fun v => rfl`. Unfold `sigInt`. Use `conv_lhs => rw [← hmap]`.

Rewrite using `[integral_map_equiv, ← hL, ← LinearIsometry.integral_comp_comm]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hconc] with x hx`. Establish `h1 : Matrix.of (e x) = g * Matrix.of x` using `rfl`. Rewrite using `[h1, ← Matrix.mul_assoc, hgg', Matrix.one_mul, X.rep.1.2 g hg _ hx, map_smul]`.

Both sides reduce to the same expression.
-/
theorem sigInt_translate {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (X : SigData k r)
    {g : Mat k r} (hg : g ∈ GV k r) (φ : Mat k r → ℂ) :
    sigInt D X (fun y => φ (g⁻¹ * y)) X.w = X.σ g (sigInt D X φ X.w) := by
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  let e := lmulME (k := k) (r := r) g g⁻¹ hgg hgg'
  have hmap : D.μG.map e = D.μG := D.haarG.left g hg
  have hconc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r := ae_iff.mpr D.haarG.conc
  let L : X.Hs →ₗᵢ[ℂ] X.Hs :=
    { toLinearMap := (X.σ g).toLinearMap, norm_map' := fun v => X.rep.2.1 g hg v }
  have hL : ∀ v, L v = X.σ g v := fun v => rfl
  unfold sigInt
  conv_lhs => rw [← hmap]
  rw [integral_map_equiv, ← hL, ← LinearIsometry.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [hconc] with x hx
  have h1 : Matrix.of (e x) = g * Matrix.of x := rfl
  rw [h1, ← Matrix.mul_assoc, hgg', Matrix.one_mul, X.rep.1.2 g hg _ hx, map_smul]
  rfl

end Cut0Aux

/- English proof (translation)
Introduce `k r Wp _ _ _ D X g hg v hv`. Take `⟨φ, hφ, rfl⟩` from `hv`. Conclude with `⟨fun y => φ (g⁻¹ * y), Cut0Aux.isTestG_translate hg hφ, (Cut0Aux.sigInt_translate D X hg φ).symm⟩`.
-/
theorem stCut0 (h : UnitaryGroupStructuralFacts) : StCut0 := by
  intro k r Wp _ _ _ D X g hg v hv
  obtain ⟨φ, hφ, rfl⟩ := hv
  exact ⟨fun y => φ (g⁻¹ * y), Cut0Aux.isTestG_translate hg hφ, (Cut0Aux.sigInt_translate D X hg φ).symm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
