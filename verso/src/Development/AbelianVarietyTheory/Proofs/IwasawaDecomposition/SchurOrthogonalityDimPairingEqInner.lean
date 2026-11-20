import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.TopSchur

/- English proof (translation)
Assemble the required witnesses or components as `⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩`.
-/
theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

/- English proof (translation)
Establish `hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0`. Introduce `τ`. Assume the negation of the conclusion as `hz`. Use `push_neg at hz`. Apply `hpr` to reduce the goal to its premises.

Establish `hs : ∀ s : SmT M, s = 0`. Introduce `s`. Proceed by induction on `s using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Rewrite using `[(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]`.

Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Use `LinearMap.ext fun w => LinearMap.ext fun s => ?_` and prove the remaining obligations. Rewrite using `[hs s]`. Simplify using the standard rewrite rules. Use `choose v hv using hτ`.

Use `⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hv τ (Subtype.ext h0)`.
-/
theorem exists_vec_prod_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {W : Type}
    [AddCommGroup W] [Module ℂ W] (pr : W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (hpr : pr ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical
  have hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0 := by
    intro τ
    by_contra hz
    push_neg at hz
    apply hpr
    have hs : ∀ s : SmT M, s = 0 := by
      intro s
      induction s using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine LinearMap.ext fun w => LinearMap.ext fun s => ?_
    rw [hs s]
    simp
  choose v hv using hτ
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩
  intro h0
  exact hv τ (Subtype.ext h0)

/- English proof (translation)
Substitute `hq` using the available equality. Clear the denominators using the available nonvanishing facts. Take the linear combination `hI`.
-/
theorem alg_step {d I p q x : ℂ} (hd : d ≠ 0) (hI : d * I = q * x) (hq : q = p) : I = x / d * p := by
  subst hq
  field_simp
  linear_combination hI

/- English proof (translation)
Substitute `hP hc` using the available equality. Clear the denominators using the available nonvanishing facts.
-/
theorem dualNumber_unit_mul_decomposition {P c d x : ℂ} (hP : P = d) (hc : c = x / d) (hd : d ≠ 0) : P * c = x := by
  subst hP hc
  field_simp

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'`. Establish `hC` using `GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models D G Pl0 T A Ks R F hB`. Use `haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1`. Establish `hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0`. Use `Module.finrank_pos (R := ℂ) (M := R.cX.W)` as an intermediate fact.

Conclude with `this.ne'` after adjusting the coercions. Establish `hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ)`. Rewrite using `[hC]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `key : ∀ v v' : R.MX.Vec, IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) * R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧ ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tp …`. Introduce `v v'`. Establish `hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ` using `riesz (R.prX.flip _)`. Establish `hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ` using `riesz (R.prX.flip _)`. Take `⟨a, ha⟩` from `hr`.

Take `⟨a', ha'⟩` from `hr'`. Establish `hA` using `GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t h h' a a'`. Take `⟨hint, hval⟩` from `hA`. Establish `hab` using `GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod D G Pl0 T A Ks R F hB hP v v' a a' ha ha'`. Simplify using `only [ha, ha']`.

Use `⟨hint, ?_⟩` and prove the remaining obligations. Conclude with `alg_step hd0 hval hab`. Establish `hv` using `exists_vec_prod_ne R.MX R.prX hB.models.prX.1`. Take `⟨v0, hv0⟩` from `hv`. Unfold `ipMT Mult.ipM`.

Use `split_ifs with hex`. Establish `e1` using `(hex.choose_spec v0 v0).2`. Establish `hch : hex.choose * _ = _ * _` using `e1.symm.trans (key v0 v0).2`. Establish `hch'` using `mul_right_cancel₀ hv0 hch`. Conclude with `dualNumber_unit_mul_decomposition hcast hch' hd0`.

It suffices to derive a contradiction. Conclude with `hex ⟨_, fun v v' => key v v'⟩`.
-/
theorem topSchur : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'
  classical
  have hC := GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models D G Pl0 T A Ks R F hB
  haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1
  have hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0 := by
    have := Module.finrank_pos (R := ℂ) (M := R.cX.W)
    exact_mod_cast this.ne'
  have hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ) := by
    rw [hC]; push_cast; rfl
  have key : ∀ v v' : R.MX.Vec,
      IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧
      ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v') ∂(R.νX t) =
      ⟪h, h'⟫_ℂ / (Module.finrank ℂ R.cX.W : ℂ) * ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
    intro v v'
    have hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    have hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    obtain ⟨a, ha⟩ := hr
    obtain ⟨a', ha'⟩ := hr'
    have hA := GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t h h' a a'
    obtain ⟨hint, hval⟩ := hA
    have hab := GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod D G Pl0 T A Ks R F hB hP v v' a a' ha ha'
    simp only [ha, ha']
    refine ⟨hint, ?_⟩
    exact alg_step hd0 hval hab
  have hv := exists_vec_prod_ne R.MX R.prX hB.models.prX.1
  obtain ⟨v0, hv0⟩ := hv
  unfold ipMT Mult.ipM
  split_ifs with hex
  · have e1 := (hex.choose_spec v0 v0).2
    have hch : hex.choose * _ = _ * _ := e1.symm.trans (key v0 v0).2
    have hch' := mul_right_cancel₀ hv0 hch
    exact dualNumber_unit_mul_decomposition hcast hch' hd0
  · exfalso
    exact hex ⟨_, fun v v' => key v v'⟩

end GlobalTheory.Mem.TopSchur
