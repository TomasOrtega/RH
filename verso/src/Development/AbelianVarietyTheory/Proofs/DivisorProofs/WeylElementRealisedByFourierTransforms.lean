import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Simplify using `[AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]`.
-/
theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]`.
-/
theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel

open GlobalTheory.TowU.WeylModel in

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ _`. Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _`.

Use `haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩`. Set `μ : Measure (κ → AF F)` to `Measure.addHaar`. Apply the tactic sequence `let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) := { toFun := fun p => Sum.elim p.1 p.2 invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr) left_inv := fun p => by simp right_inv := fun x => by simp map_add' := fun p q => by funext i; cases i <;> rfl }`. Establish `hc : Continuous E` using `(Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous`. Establish `hc' : Continuous E.symm` using `(Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous`.

Set `H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F)` to `{ toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }`. Set `ν : Measure (κ ⊕ κ → AF F)` to `Measure.map E (μ.prod μ)`. Use `haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'`. Set `ε₁ : κ → ℤˣ` to `fun _ => 1`. Set `ε₂ : κ ⊕ κ → ℤˣ` to `Sum.elim (fun _ => 1) (fun _ => -1)`.

Take `⟨S, S', hS, hSf⟩` from `GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁`. Take `⟨Sd, Sd', hSd, hSdf⟩` from `GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂`. Use `⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩` and prove the remaining obligations. Use `hS using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`.

Rewrite using `[act_weyl]`. Apply the tactic sequence `refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]`. Use `hSd using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Apply the tactic sequence `refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>`.

Simplify using `[dblAct, act_weyl, ε₂]`. Use function extensionality and compare the values at `y`. Establish `hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ)` using `rfl`. Establish `e₂ : star (S (star φ₂)) (y ∘ Sum.inr) = ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ`. Rewrite using `[Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]`. Rewrite using `[hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]`. Express the relevant statement in the definitionally equal form `_ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)`.

Rewrite using `[e₂, hSf φ₁ h₁, ← integral_prod_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _`. Establish `es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i = ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i + -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i)`. Simplify using `[Fintype.sum_sum_type, ε₁, ε₂]`.

Rewrite using `[es, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
