import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

/- English proof (translation)
Conclude with `cj_mem M.val h`.
-/
private theorem cj_val {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : cj M M.val x = x := by
  exact cj_mem M.val h

/- English proof (translation)
Establish `hx : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `: IsAlgebraic ℚ (e.toRatAlgHom x)` using `hx.algHom _`. Conclude with `mem_algebraicClosure_iff.mpr this`.
-/
private theorem emb_mem_Qbar (D : D7) (e : D.host.E →+* ℂ) (x : D.host.E) : e x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ (e.toRatAlgHom x) := hx.algHom _
  exact mem_algebraicClosure_iff.mpr this

/- English proof (translation)
Unfold `U1`. Use `fun_prop`.
-/
private theorem differentiable_U1 (Λ : AddSubgroup ℂ) (ω : ℂ) {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U1 Λ ω G) := by
  unfold U1
  fun_prop

/- English proof (translation)
Establish `hP` using `(GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.1`. Use function extensionality and compare the values at `z`. Unfold `U U1 pullB Hf`. Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]`. Use `congr 1`.

Simplify using `only [coordB_add]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = ∑ j, (_ / (area (tor0 D cc δ).abelian₂ : ℂ) - _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ)))`. Rewrite using `[Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem U_pullB_eq_prod (D : D7) (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) (g : ℂ → ℂ) (t : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) = fun z =>
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  have hP := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.1
  funext z
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · simp only [coordB_add]
  · congr 1
    change _ = ∑ j, (_ / (area (tor0 D cc δ).abelian₂ : ℂ) - _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ)))
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Introduce `D cc δ hC N N' r b hb F hF`. Establish `h : admG1 D` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `hlat` using `(GlobalTheory.CurveLattice.lattice_of_curve D h cc δ hC).1`. Establish `hσ : Differentiable ℂ (sgStar (lamOf D cc δ))` using `(GlobalTheory.OddTheta.sgStar_laws _ hlat).1.1`. Establish `hL` using `(GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.2.1`.

Unfold `Tr at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨t, ⟨m, hm, hmt⟩, rfl⟩` from `hF`. Express the relevant statement in the definitionally equal form `Differentiable ℂ (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) ∧ CoefIn D (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) Qbar`.

Rewrite using `[U_pullB_eq_prod D h cc δ hb]`. Establish `hq : ∀ j, InRationalLattice (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t)` using `fun j => by`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← coordB_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `(hL _).1 hmt j`.

Establish `hl : ∀ j τ a c, (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)) ∈ Qbar` using `fun j τ a c => by`. Express the relevant statement in the definitionally equal form `(starRingEnd ℂ) (embT D τ (b j a c)) ∈ Qbar`. Rewrite using `[← emb_conj]`. Conclude with `emb_mem_Qbar D _ _`. Establish `key` using `GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj D N N' r Qbar Qbar.val (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ))) (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ))) (fun j τ a c => (starRingEnd ℂ) ( …`.

Use `(GlobalTheory.T.forall_use1 D cc δ hC).1 _ (hq j) n` as an intermediate fact. Conclude with `⟨this, (cj_val this).symm⟩)`. Use the proof step `(fun j τ a c => ⟨hl j τ a c, (cj_val (hl j τ a c)).symm⟩)`. Conclude with `⟨key.1, fun α => (key.2.2 α).1⟩`. Consider the case `zero => exact ⟨differentiable_const 0, fun α => by rw [taylor_zero]; exact zero_mem _⟩`.

Consider the case `add F G _ _ hF hG`. Conclude with `⟨hF.1.add hG.1, fun α => by`. Rewrite using `[taylor_add D hF.1 hG.1]`. Conclude with `add_mem (hF.2 α) (hG.2 α)⟩`. Consider the case `smul c F _ hF`.

Establish `: c • F = fun z => (c : ℂ) * F z` using `rfl`. Rewrite using `[this]`. Conclude with `⟨hF.1.const_mul _, fun α => by`. Rewrite using `[taylor_mul D _ hF.1]`. Conclude with `mul_mem c.2 (hF.2 α)⟩`.
-/
theorem translates_coef_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, Differentiable ℂ F ∧ CoefIn D F Qbar := by
  intro D cc δ hC N N' r b hb F hF
  have h : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D h cc δ hC).1
  have hσ : Differentiable ℂ (sgStar (lamOf D cc δ)) := (GlobalTheory.OddTheta.sgStar_laws _ hlat).1.1
  have hL := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.2.1
  unfold Tr at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨t, ⟨m, hm, hmt⟩, rfl⟩ := hF
    change Differentiable ℂ (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) ∧
      CoefIn D (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) Qbar
    rw [U_pullB_eq_prod D h cc δ hb]
    have hq : ∀ j, InRationalLattice (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) := fun j => by
      refine ⟨m, hm, ?_⟩
      rw [← coordB_smul, Nat.cast_smul_eq_nsmul]
      exact (hL _).1 hmt j
    have hl : ∀ j τ a c, (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)) ∈ Qbar := fun j τ a c => by
      change (starRingEnd ℂ) (embT D τ (b j a c)) ∈ Qbar
      rw [← emb_conj]
      exact emb_mem_Qbar D _ _
    have key := GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj D N N' r Qbar Qbar.val
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j => differentiable_U1 _ _ hσ) (fun j => differentiable_U1 _ _ hσ)
      (fun j n => by
        have := (GlobalTheory.T.forall_use1 D cc δ hC).1 _ (hq j) n
        exact ⟨this, (cj_val this).symm⟩)
      (fun j τ a c => ⟨hl j τ a c, (cj_val (hl j τ a c)).symm⟩)
    exact ⟨key.1, fun α => (key.2.2 α).1⟩
  | zero => exact ⟨differentiable_const 0, fun α => by rw [taylor_zero]; exact zero_mem _⟩
  | add F G _ _ hF hG =>
    exact ⟨hF.1.add hG.1, fun α => by
      rw [taylor_add D hF.1 hG.1]; exact add_mem (hF.2 α) (hG.2 α)⟩
  | smul c F _ hF =>
    have : c • F = fun z => (c : ℂ) * F z := rfl
    rw [this]
    exact ⟨hF.1.const_mul _, fun α => by
      rw [taylor_mul D _ hF.1]; exact mul_mem c.2 (hF.2 α)⟩

end GlobalTheory.ThetaConj
