import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
import GroundTheory.AutomorphicForms.FourierWhittaker

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

namespace UpperTheory.ConvolutionTheory.R2.Pp

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn]`.
-/
theorem n_zero : gl (nU (0 : A F)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`. Establish `e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q))` using `fun q => inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])`. Simplify using `only [e]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`.
-/
theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

/- English proof (translation)
Use `⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap F (A F) (!![1, k; 0, 1] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn]`.
-/
theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨!![(t : F), 0; 0, 1], !![((t⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, Units.ext ?_⟩`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap F (A F) (!![(t : F), 0; 0, 1] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aE]`.
-/
theorem rat_a (t : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = aE (IdeleGroup.diagonal F t) := by
  refine ⟨⟨!![(t : F), 0; 0, 1], !![((t⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(t : F), 0; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem a_n (t : (A F)ˣ) (b : A F) : aE t * gl (nU b) = gl (nU ((t : A F) * b)) * aE t := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[ψ, AddChar.map_add_eq_mul]`.
-/
theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
Simplify using `[ψ, adelicChar_algebraMap]`.
-/
theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
theorem norm_ψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp continuous_adelicChar`.
-/
theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F), fun _ hx => ⟨subset_closure hx.1, hx.2⟩⟩`.
-/
theorem exists_cpt : ∃ C : Set (A F), IsCompact C ∧ fundamentalSet F ⊆ C :=
  ⟨_, (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
    fun _ hx => ⟨subset_closure hx.1, hx.2⟩⟩

/- English proof (translation)
Establish `hp` using `measurePreserving_funUnique (adeleMeasure F) ι`. Establish `e : vecDomain F ι = MeasurableEquiv.funUnique ι (A F) ⁻¹' fundamentalSet F`. Use extensionality with `x`. Conclude with `⟨fun hx => hx default trivial, fun hx i _ => by rw [Unique.eq_default i]; exact hx⟩`. Rewrite using `[e]`.

Use `hp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) h (fundamentalSet F) using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | congr!`.
-/
theorem int_one {ι : Type} [Fintype ι] [Unique ι] (h : A F → ℂ) :
    ∫ x in vecDomain F ι, h (x default) ∂(vecMeasure F ι) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hp := measurePreserving_funUnique (adeleMeasure F) ι
  have e : vecDomain F ι = MeasurableEquiv.funUnique ι (A F) ⁻¹' fundamentalSet F := by
    ext x
    exact ⟨fun hx => hx default trivial, fun hx i _ => by rw [Unique.eq_default i]; exact hx⟩
  rw [e]
  convert hp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) h (fundamentalSet F) using 2
  all_goals first | rfl | congr!

/- English proof (translation)
Rewrite using `[← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h]`. Use `setIntegral_comp_add (fun _ => a) (h := fun x => h (x default)) fun ξ hξ x => ?_` and prove the remaining obligations. Take `⟨η, rfl⟩` from `mem_vecLattice.1 hξ`. Conclude with `hh _ _`.
-/
theorem int_add {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (a : A F) :
    ∫ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h]
  refine setIntegral_comp_add (fun _ => a) (h := fun x => h (x default)) fun ξ hξ x => ?_
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  exact hh _ _

/- English proof (translation)
Rewrite using `[← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h, ← setIntegral_comp_matVec (Matrix.GeneralLinearGroup.scalar (Fin 1) t) (f := fun x => h (x default)) fun ξ hξ x => by`. Take `⟨η, rfl⟩` from `mem_vecLattice.1 hξ`. Conclude with `hh _ _]`. Simplify using `[matVec_apply]`.
-/
theorem int_mul {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (t : Fˣ) :
    ∫ b in fundamentalSet F, h (rt (t : F) * b) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h,
    ← setIntegral_comp_matVec (Matrix.GeneralLinearGroup.scalar (Fin 1) t) (f := fun x => h (x default)) fun ξ hξ x => by
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      exact hh _ _]
  simp [matVec_apply]

/- English proof (translation)
Take `⟨γ, hγ⟩` from `rat_n k`. Rewrite using `[n_add, ← hγ, mul_assoc, hf.2]`.
-/
theorem Lf.per {f : GL (Fin 2) (A F) → ℂ} (hf : Lf f) (k : F) (x : A F) (g : GL (Fin 2) (A F)) :
    f (gl (nU (rt k + x)) * g) = f (gl (nU x) * g) := by
  obtain ⟨γ, hγ⟩ := rat_n k
  rw [n_add, ← hγ, mul_assoc, hf.2]

/- English proof (translation)
Take `⟨C, hC, hs⟩` from `exists_cpt (F := F)`. Conclude with `(hc.continuousOn.integrableOn_compact hC).mono_set hs`.
-/
theorem intOn {h : A F → ℂ} (hc : Continuous h) : IntegrableOn h (fundamentalSet F) (adeleMeasure F) := by
  obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hs

/- English proof (translation)
Use `norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure F) (s := fundamentalSet F) (f := fun b => f (gl (nU b) * g) * ψ b) (C := B) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top) fun b _ => by rw [norm_mul, norm_ψ, mul_one]; exact h b` as an intermediate fact. Rewrite `this` using `[measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem norm_Wf_le {f : GL (Fin 2) (A F) → ℂ} {g : GL (Fin 2) (A F)} {B : ℝ} (h : ∀ b, ‖f (gl (nU b) * g)‖ ≤ B) :
    ‖Wf f g‖ ≤ B := by
  have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure F) (s := fundamentalSet F)
    (f := fun b => f (gl (nU b) * g) * ψ b) (C := B) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top)
    fun b _ => by rw [norm_mul, norm_ψ, mul_one]; exact h b
  rwa [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one] at this

end UpperTheory.ConvolutionTheory.R2.Pp
