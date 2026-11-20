import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU
open GlobalTheory.AdelicSvN GlobalTheory.AdelicSvNLevi

namespace GlobalTheory.TowU.LeviModel

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isOp_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix ι ι (AF F) := A.map (algebraMap F (AF F))
  let Aim : Matrix ι ι (AF F) := A⁻¹.map (algebraMap F (AF F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine
    { pres := comp_mem A⁻¹ A h2 h1
      pres' := comp_mem A A⁻¹ h1 h2
      left := fun φ _ => funext fun x => ?_
      right := fun φ _ => funext fun x => ?_
      adm := fun l hl g hg => ?_
      adm' := fun l hl g hg => ?_
      Heisenberg₂ := fun w φ _ => funext fun x => ?_
      theta := ⟨1, one_ne_zero, fun φ _ => ?_⟩
      norm := fun μ μ' hμ hμ' => ?_ }
  · change φ (Aim *ᵥ (Am *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A A⁻¹ h1 h2).continuous,
      hg.2.comp_homeomorph (finHomeo A A⁻¹ h1 h2)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A A⁻¹ h1 h2)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A A⁻¹ h1 h2, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · rw [one_mul]
    unfold thetaSum
    let e : (ι → F) ≃ (ι → F) :=
      { toFun := fun ξ => A⁻¹ *ᵥ ξ
        invFun := fun ξ => A *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    have he := Equiv.tsum_eq e (fun ξ : ι → F => φ fun i => algebraMap F (AF F) (ξ i))
    refine Eq.trans (tsum_congr fun ξ => ?_) he
    change φ (Aim *ᵥ _) = φ (fun i => algebraMap F (AF F) ((A⁻¹ *ᵥ ξ) i))
    congr 1
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) A⁻¹ ξ i).symm
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    letI : MeasurableSpace (ι → AF F) := borel _
    haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
    let L : (ι → AF F) ≃+ (ι → AF F) :=
      { toFun := fun x => Aim *ᵥ x
        invFun := fun x => Am *ᵥ x
        left_inv := fun x => by simp only [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
        right_inv := fun x => by simp only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
        map_add' := fun x y => Matrix.mulVec_add _ _ _ }
    have hc : Continuous L := continuous_const.matrix_mulVec continuous_id
    have hc' : Continuous L.symm := continuous_const.matrix_mulVec continuous_id
    let H : (ι → AF F) ≃ₜ (ι → AF F) := { toEquiv := L.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
    haveI : (Measure.map L μ').IsAddHaarMeasure := L.isAddHaarMeasure_map μ' hc hc'
    have e := Measure.isAddLeftInvariant_eq_smul (Measure.map L μ') μ
    refine ⟨Measure.addHaarScalarFactor (Measure.map L μ') μ, ?_, ENNReal.coe_ne_top, fun φ _ => ?_⟩
    · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.map L μ') μ).ne'
    · have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) H.toMeasurableEquiv (μ := μ')
      change ∫⁻ x, ‖φ (Aim *ᵥ x)‖ₑ ^ 2 ∂μ' = _
      have hL : (Measure.map H.toMeasurableEquiv μ') = Measure.map L μ' := rfl
      rw [hL, e, lintegral_smul_measure] at hm
      exact hm.symm.trans rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem inv_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A 0 0 A)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA]
  simp [Matrix.fromBlocks_one]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem dblAct_levi {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    dblAct (AdelicSvN.act (R := AF F) (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) =
      AdelicSvN.act (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 A) 0 0 (Matrix.fromBlocks A 0 0 A)⁻¹ᵀ) := by
  funext w
  rw [inv_diag A hA, act_levi, Matrix.fromBlocks_transpose]
  simp only [dblAct, act_levi, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.transpose_zero, Matrix.mulVec_neg, neg_neg]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem isOp2_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp2 ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have hA2 : IsUnit (Matrix.fromBlocks A 0 0 A).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hA
  refine ⟨isOp_levi ψ A hA, compM (Matrix.fromBlocks A 0 0 A)⁻¹, compM (Matrix.fromBlocks A 0 0 A), ?_,
    fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_levi A hA]; exact isOp_levi ψ _ hA2
  · funext x
    rw [inv_diag A hA]
    change boxFun φ₁ φ₂ _ = φ₁ _ * star (star (φ₂ _))
    rw [star_star]
    simp only [boxFun, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add]
    rfl

end GlobalTheory.TowU.LeviModel

open GlobalTheory.TowU.LeviModel in

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem GlobalTheory.TowU.realised_levi2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det →
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' :=
  fun _ _ _ ψ _ _ _ _ A hA => ⟨_, _, isOp2_levi ψ A hA⟩

end
