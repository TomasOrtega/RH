import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGenericRepresentation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticSplittingUniqueUpToCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealLiftCharacterTraceHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement

section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.LieScal
open scoped Classical in
/- English proof (translation)
Introduce `hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom`. Take `⟨ω₀, c₀, hH, hc, hact⟩` from `_root_.GlobalTheory.T.isGeneric_localComponent hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ`. Take `⟨ν, hν, hmul, hνc, hν0⟩` from `_root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character hP F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc`. Take `⟨k, hk⟩` from `_root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt hP F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0`. Use `⟨fun w => c₀ w + k w, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ Y hY T g hg l hl`. Establish `hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1)` using `fun t => hγ.2 _`. Establish `hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ` using `fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) = fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))`. Use function extensionality and compare the values at `t`.

Rewrite using `[hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]`. Use `show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0`. Rewrite using `[e1]`. Establish `h3` using `(hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)`. Establish `hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1` using `by rw [ofAdd_zero, map_one]`.

Establish `h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1)` using `fun u _ => by simp`. Establish `hν1 : ν 1 = 1`. Use `hmul 1 1 h1m h1m` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `(mul_eq_left₀ (hν0 1 h1m)).mp this.symm`.

Use `beta_reduce at h3`. Rewrite `h3` using `[hγ0, hν1, map_one, Module.End.one_apply, one_mul]`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Establish `e2 : sumPl (fun w => fockAct2 P Q R S (Y w) + (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) = sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) + (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (Tens F P Q R S))`. Simplify using `only [add_mul, add_smul, ← add_assoc]`.

Conclude with `sumPl_add_smul (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _`. Rewrite using `[e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]`. Establish `key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g`. Introduce `z f f'`. Use function extensionality and compare the values at `x`.

Simplify using `[pureA]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, map_add, map_smul, smul_eq_mul]`.
-/
theorem lie_algebra_acts_by_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine → LieScalar := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := _root_.GlobalTheory.T.isGeneric_localComponent hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := _root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character hP F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt hP F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 P Q R S (Y w) + (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (Tens F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact sumPl_add_smul (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add, map_smul, smul_eq_mul]
end GlobalTheory.LieScal
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | exact _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | (intros; apply _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weil_lie_algebra_scalar_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @_root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | exact _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | (intros; apply _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar <;> assumption)
end
