import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

namespace StandardDualMassAtPoint

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
/- English proof (translation)
Simplify using `[segre]`.
-/
theorem segre_const (z : (Σ _ : Unit, T) → ℂ) (t : T) :
    segre (ι := dualBlocks T) z (fun _ => t) = z ⟨(), t⟩ := by
  simp [segre]

omit [Fintype T] [DecidableEq T] in
open Classical in

/- English proof (translation)
Rewrite using `[dualRecover, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]`. Use function extensionality and compare the values at `t`. Simplify using `[Matrix.mulVec, dotProduct, dualEmbMatrix, dualPlanePt, Fintype.sum_prod_type]`.
-/
theorem recover_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualRecover b hb (fun t => dualPlanePt b σ v ⟨(), t⟩) =
      fun p => if p.1 = σ then v p.2 else 0 := by
  rw [dualRecover, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  funext t
  simp [Matrix.mulVec, dotProduct, dualEmbMatrix, dualPlanePt,
    Fintype.sum_prod_type]

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [dualProj_apply, segre_const, recover_planePt]`. Rewrite using `[Finset.sum_eq_single σ (fun τ _ hτ => if_neg hτ) (by simp)]`. Conclude with `if_pos rfl`.
-/
theorem proj_segre_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualProj b hb (segre (dualPlanePt b σ v)) = v := by
  funext j
  simp only [dualProj_apply, segre_const, recover_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg hτ) (by simp)]
  exact if_pos rfl

/- English proof (translation)
Take `⟨σ, hσ⟩` from `hOn K (D + 1) F T b hb z hz`. Establish `hp : ∀ j, dualProj b hb (segre z) j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)`. Introduce `j`. Simplify using `only [dualProj_apply, segre_const]`. Conclude with `Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)`.

Use `show Real.sqrt (dualNormSq b hb _) = _`. Use `congr 1`. Rewrite using `[dualNormSq, Finset.sum_eq_single σ]`. Rewrite using `[hF, one_mulVec, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hp]`. Introduce `τ _ hτ`. Establish `h0 : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j)) = 0` using `funext (hσ τ hτ)`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem h_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    (hz : z ∈ mcPts (dualIdeal b)) :
    (dualLine F b hb).h z = Real.sqrt (∑ j, ‖dualProj b hb (segre z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hp : ∀ j, dualProj b hb (segre z) j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
    intro j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  show Real.sqrt (dualNormSq b hb _) = _
  congr 1
  rw [dualNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, hp]
  · intro τ _ hτ
    have h0 : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j)) = 0 := funext (hσ τ hτ)
    rw [h0]
    simp
  · simp

/- English proof (translation)
Unfold `sheetDensity`. Rewrite using `[dif_pos h, one_mul]`. Apply `maDensity_congr_of_eventuallyEq` to reduce the goal to its premises. Introduce `j`. Use `filter_upwards [h.choose_spec.2] with y' hy'`.

Take `⟨-, hmc, hΨ⟩` from `hy'`. Use `show Real.log ((dualLine F b hb).h (h.choose y')) = gbPot y'`. Rewrite using `[h_eq hOn hF b hb hmc, hΨ, gbPot, Fin.sum_univ_succ]`. Simplify using the standard rewrite rules.
-/
theorem sheetDensity_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {y : Fin D → ℂ}
    {w : ((k : Unit) → dualBlocks T k) → ℂ} (h : ∃ γ, IsSheet (dualIdeal b) (dualProj b hb) y w γ) :
    sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((dualLine F b hb).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF b hb hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl, hΨ⟩`. Take `⟨σ, hσ⟩` from `hOn K (D + 1) F T b hb z hz`. Use `⟨σ, congrArg segre ?_⟩` and prove the remaining obligations.

Establish `hW : dualRecover b hb (fun t => z ⟨(), t⟩) = dualRecover b hb (fun t => dualPlanePt b σ (Fin.cons 1 y) ⟨(), t⟩)`. Rewrite using `[recover_planePt]`. Use function extensionality and compare the values at `⟨τ, j⟩`. Distinguish the cases in `hτ : τ = σ`. Substitute `hτ` using the available equality.

Rewrite using `[if_pos rfl, ← hΨ]`. Simplify using `only [dualProj_apply, segre_const]`. Conclude with `(Finset.sum_eq_single τ (fun τ' _ h' => hσ τ' h' j) (by simp)).symm`. Rewrite using `[if_neg hτ]`. Conclude with `hσ τ hτ j`.

Establish `h1` using `(dualRecover b hb).injective hW`. Use function extensionality and compare the values at `⟨u, t⟩`. Consider the cases of `u`. Conclude with `(congrFun h1 t).symm`. Introduce and unpack `⟨σ, rfl⟩`.

Establish `hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0` using `fun h0 => by simpa using congrFun h0 0`. Conclude with `⟨_, hOf K (D + 1) F T b hb σ _ hv, rfl, proj_segre_planePt b hb σ _⟩`.
-/
theorem fibre_eq (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) {D : ℕ}
    {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    fibre (dualIdeal b) (dualProj b hb) y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
        dualRecover b hb (fun t => dualPlanePt b σ (Fin.cons 1 y) ⟨(), t⟩) := by
      rw [recover_planePt]
      funext ⟨τ, j⟩
      by_cases hτ : τ = σ
      · subst hτ
        rw [if_pos rfl, ← hΨ]
        simp only [dualProj_apply, segre_const]
        exact (Finset.sum_eq_single τ (fun τ' _ h' => hσ τ' h' j) (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ hτ j
    have h1 := (dualRecover b hb).injective hW
    funext ⟨u, t⟩
    cases u
    exact (congrFun h1 t).symm
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) F T b hb σ _ hv, rfl, proj_segre_planePt b hb σ _⟩

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Introduce `σ τ h`. Establish `h1` using `congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ => dualRecover b hb (fun t => w fun _ => t)) h`. Simplify using `only [segre_const, recover_planePt] at h1`. Establish `h2` using `congrFun h1 (σ, 0)`. Simplify using `using h2`.
-/
theorem planePt_injective {D : ℕ} {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  have h2 := congrFun h1 (σ, 0)
  simpa using h2

/- English proof (translation)
Establish `hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ))`. Rewrite using `[differentiable_pi]`. Introduce `j`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `using differentiable_apply (𝕜 := ℂ) k`. Use `⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt b hb σ _⟩⟩` and prove the remaining obligations. Use `(differentiable_pi.mpr fun p => ?_) y'` and prove the remaining obligations. Simplify using `only [dualPlanePt]`. Conclude with `Differentiable.fun_sum fun j _ => (differentiable_pi.mp hc j).const_mul _`.

Conclude with `hOf K (D + 1) F T b hb σ _ fun h0 => by simpa using congrFun h0 0`.
-/
theorem isSheet_planePt (hOf : DualPtsOfPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (dualIdeal b) (dualProj b hb) y (segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt b hb σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt]
    exact Differentiable.fun_sum fun j _ => (differentiable_pi.mp hc j).const_mul _
  · exact hOf K (D + 1) F T b hb σ _ fun h0 => by simpa using congrFun h0 0

end StandardDualMassAtPoint

open StandardDualMassAtPoint in

/- English proof (translation)
Introduce `K _ _ D F T _ _ b hb hF`. Establish `hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) (dualProj b hb) y, sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y`. Introduce `y`. Rewrite using `[fibre_eq hOn hOf b hb y, finsum_mem_range (planePt_injective b hb y), finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF b hb ⟨_, isSheet_planePt hOf b hb σ y⟩, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Unfold `ptsIntegralAt`.

Simplify using `only [hint]`. Rewrite using `[integral_const_mul, integral_maDensity_gbPot, mul_one]`.
-/
theorem DualStdMassAt.proof (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) :
    DualStdMassAt.Statement := by
  intro K _ _ D F T _ _ b hb hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) (dualProj b hb) y,
      sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf b hb y, finsum_mem_range (planePt_injective b hb y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF b hb ⟨_, isSheet_planePt hOf b hb σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]

end

end GroundTheory.Heights₂.Heights
