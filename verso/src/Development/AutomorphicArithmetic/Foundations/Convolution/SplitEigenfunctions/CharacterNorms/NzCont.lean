import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `(TR.continuous_infEq ℚ).prodMk continuous_const`.
-/
theorem cont_sInf : Continuous (TR.sInf ℚ) :=
  (TR.continuous_infEq ℚ).prodMk continuous_const

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `e : ∀ t, (rot t).val i j = (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) + TR.sInf ℚ ((X t).val i j)`. Introduce `t`. Rewrite using `[rot_eq]`. Both sides reduce to the same expression.

Simplify using `only [e]`. Use `continuous_const.add (cont_sInf.comp ?_)` and prove the remaining obligations. Use `continuous_pi fun w => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [X] <;> fun_prop`.
-/
theorem cont_rotval : Continuous fun t : ℝ => (rot t).val := by
  refine continuous_matrix fun i j => ?_
  have e : ∀ t, (rot t).val i j = (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
      TR.sInf ℚ ((X t).val i j) := by
    intro t
    rw [rot_eq]
    rfl
  simp only [e]
  refine continuous_const.add (cont_sInf.comp ?_)
  refine continuous_pi fun w => ?_
  fin_cases i <;> fin_cases j <;> simp [X] <;> fun_prop

/- English proof (translation)
Rewrite using `[rot_eq, rot_eq, X_neg, map_inv]`.
-/
theorem rot_neg (t : ℝ) : rot (-t) = (rot t)⁻¹ := by
  rw [rot_eq, rot_eq, X_neg, map_inv]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨cont_rotval, ?_⟩` and prove the remaining obligations. Establish `e : (fun t => ((rot t)⁻¹).val) = (fun t => (rot t).val) ∘ Neg.neg`. Use function extensionality and compare the values at `t`. Simplify using `[rot_neg]`. Express the relevant statement in the definitionally equal form `Continuous fun t => ((rot t)⁻¹).val`.

Rewrite using `[e]`. Conclude with `cont_rotval.comp continuous_neg`.
-/
theorem cont_rot : Continuous rot := by
  refine Units.continuous_iff.2 ⟨cont_rotval, ?_⟩
  have e : (fun t => ((rot t)⁻¹).val) = (fun t => (rot t).val) ∘ Neg.neg := by
    funext t
    simp [rot_neg]
  change Continuous fun t => ((rot t)⁻¹).val
  rw [e]
  exact cont_rotval.comp continuous_neg

/- English proof (translation)
The claim follows from `Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)`.
-/
theorem cont_em : Continuous (em E) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ)`. Use function extensionality and compare the values at `y`. Conclude with `iy_coe y.2`.

Express the relevant statement in the definitionally equal form `Continuous fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)`. Rewrite using `[e]`. Use `continuous_const.add (cont_sInf.comp ?_)` and prove the remaining obligations. Conclude with `continuous_pi fun _ => continuous_subtype_val`. Establish `e : (fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ)⁻¹`.

Use function extensionality and compare the values at `y`. Conclude with `iy_inv_coe y.2`. Express the relevant statement in the definitionally equal form `Continuous fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)`. Rewrite using `[e]`. Use `continuous_const.add (cont_sInf.comp ?_)` and prove the remaining obligations.

Use `continuous_pi fun _ => ?_` and prove the remaining obligations. Conclude with `continuous_subtype_val.inv₀ fun y => y.2`.
-/
theorem contOn_iy : ContinuousOn iy ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : (fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ) := by
      funext y
      exact iy_coe y.2
    change Continuous fun y : ({0}ᶜ : Set ℝ) => ((iy y : (A ℚ)ˣ) : A ℚ)
    rw [e]
    refine continuous_const.add (cont_sInf.comp ?_)
    exact continuous_pi fun _ => continuous_subtype_val
  · have e : (fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)) = fun y : ({0}ᶜ : Set ℝ) => 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => (y : ℝ)⁻¹ := by
      funext y
      exact iy_inv_coe y.2
    change Continuous fun y : ({0}ᶜ : Set ℝ) => (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ)
    rw [e]
    refine continuous_const.add (cont_sInf.comp ?_)
    refine continuous_pi fun _ => ?_
    exact continuous_subtype_val.inv₀ fun y => y.2

/- English proof (translation)
Use `cont_em.comp_continuousOn (ContinuousOn.mul (continuous_aE.comp_continuousOn ?_) (cont_rot.comp continuous_snd).continuousOn)` and prove the remaining obligations. Conclude with `contOn_iy.comp continuous_fst.continuousOn fun p hp => hp.1`.
-/
theorem contOn_curve : ContinuousOn (fun p : ℝ × ℝ => em E (aE (iy p.1) * rot p.2)) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) := by
  refine cont_em.comp_continuousOn (ContinuousOn.mul (continuous_aE.comp_continuousOn ?_) (cont_rot.comp continuous_snd).continuousOn)
  exact contOn_iy.comp continuous_fst.continuousOn fun p hp => hp.1

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp <;> fun_prop`. Establish `e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q))` using `fun q => inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, nU_zero, gl_one])`. Simplify using `only [e]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`.
-/
theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, nU_zero, gl_one])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp continuous_adelicChar`.
-/
theorem cont_psi : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar

/- English proof (translation)
The claim follows from `cont_n.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const))`.
-/
theorem cont_mkE (D : Dat ℚ E) : Continuous fun x : Fin 2 → A ℚ => nE D x :=
  cont_n.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const))

/- English proof (translation)
Take `⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ fundamentalSet ℚ ⊆ B` from `⟨closure (fundamentalSetInfinite ℚ) ×ˢ _, (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ), fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩`. Establish `hC : IsCompact (Set.univ.pi fun _ : Fin 2 => B)` using `isCompact_univ_pi fun _ => hB`. Conclude with `(measure_mono (show FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => B from fun x hx i hi => hEB (hx i hi))).trans_lt hC.measure_lt_top`.
-/
theorem adelic_measure_fundamental_domain_pi_rat_lt_top : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := by
  obtain ⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ fundamentalSet ℚ ⊆ B :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin 2 => B) := isCompact_univ_pi fun _ => hB
  exact (measure_mono (show FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => B from fun x hx i hi => hEB (hx i hi))).trans_lt hC.measure_lt_top

/- English proof (translation)
Take `⟨B, hB⟩` from `hb`. Use `haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using adelic_measure_fundamental_domain_pi_rat_lt_top⟩`. Establish `hnorm : ∀ x : A ℚ, ‖ψ x‖ = 1` using `fun x => Circle.norm_coe _`. Use `continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_` and prove the remaining obligations. Introduce `x`.

Conclude with `((hφ.comp ((cont_mkE D).mul continuous_const)).mul (cont_psi.comp (continuous_apply 1))).aestronglyMeasurable`. Introduce `x`. Use `Filter.Eventually.of_forall fun u => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hnorm, mul_one]`. Conclude with `hB _`.

Use `Filter.Eventually.of_forall fun u => ?_` and prove the remaining obligations. Conclude with `(hφ.comp (continuous_const.mul hc)).mul continuous_const`.
-/
theorem cont_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hφ : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B)
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {c : T → GL (Fin 2) (A E)} (hc : Continuous c) :
    Continuous fun x => Wo D φ (c x) := by
  obtain ⟨B, hB⟩ := hb
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using adelic_measure_fundamental_domain_pi_rat_lt_top⟩
  have hnorm : ∀ x : A ℚ, ‖ψ x‖ = 1 := fun x => Circle.norm_coe _
  refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
  · intro x
    exact ((hφ.comp ((cont_mkE D).mul continuous_const)).mul (cont_psi.comp (continuous_apply 1))).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, hnorm, mul_one]
    exact hB _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (hφ.comp (continuous_const.mul hc)).mul continuous_const

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_restrict]`. Conclude with `cont_Wo D hφ hb (continuousOn_iff_continuous_restrict.1 contOn_curve)`.
-/
theorem contOn_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hφ : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) :
    ContinuousOn (fun p : ℝ × ℝ => Wo D φ (em E (aE (iy p.1) * rot p.2))) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_restrict]
  exact cont_Wo D hφ hb (continuousOn_iff_continuous_restrict.1 contOn_curve)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
