import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaZeroPeriodLatticeEq
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

/- English proof (translation)
Introduce `Λ hΛ v hv z`. Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ hΛ`. Establish `hΛL : Λ = L.lattice.toAddSubgroup` using `AddSubgroup.ext hL`. Establish `hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L` using `by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L`. Establish `hwp : wpF Λ = L.weierstrassP` using `funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)`.

Establish `hsd : Differentiable ℂ (sgStar Λ)` using `hΛ.differentiable`. Establish `hopen : IsOpen ((Λ : Set ℂ)ᶜ)`. Establish `: (Λ : Set ℂ) = (L.lattice : Set ℂ)` using `Set.ext fun w => hL w`. Rewrite using `[this]`. Conclude with `L.isClosed_lattice.isOpen_compl`.

Establish `hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w`. Introduce `w hw`. Rewrite using `[colB, hΛ.sqTh_eq hv hw, ← hwp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w`.

Introduce `w hw`. Establish `hwL : w ∉ L.lattice` using `fun h => hw ((hL w).2 h)`. Establish `hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w`. Establish `h1 : DifferentiableAt ℂ L.weierstrassP w` using `L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)`. Establish `h2` using `h1.hasDerivAt`.

Rewrite `h2` using `[L.deriv_weierstrassP]`. Then use the resulting hypothesis. Establish `hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v)` using `by filter_upwards [hopen.mem_nhds hw] with u hu`. Rewrite using `[hΛ.sqTh_eq hv hu, hwp]`. Establish `hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v)) ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) + sgStar Λ w ^ 2 * L.derivWeierstrassP w) w` using `((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)`. Rewrite using `[colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) → Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) = 2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0)`. Introduce `y hy`. Establish `h` using `Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2) (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))`.

Rewrite `h` using `[← hσ]`. Rewrite `h`, the goal using `[Matrix.det_fin_three]`. Simplify using `[Matrix.vecHead, Matrix.vecTail] at h ⊢`. Rewrite using `[hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]`. Simplify using `only [colA]`.

Take the linear combination `h`. Establish `hcA : Continuous (colA Λ)`. Use `hsd.continuous` as an intermediate fact. Unfold `colA`. Use `fun_prop`.

Establish `hcB : Continuous (colB Λ v)`. Use `(hΛ.differentiable_sqTh v).continuous` as an intermediate fact. Use `hsd.continuous` as an intermediate fact. Unfold `colB`. Use `fun_prop`.

Establish `hcC : Continuous (colC Λ v)`. Establish `h1 : Continuous (deriv (sqTh Λ v))` using `((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl`. Establish `h2 : Continuous (deriv (sgStar Λ))` using `(hsd.contDiff (n := 1)).continuous_deriv le_rfl`. Use `(hΛ.differentiable_sqTh v).continuous` as an intermediate fact. Use `hsd.continuous` as an intermediate fact.

Unfold `colC`. Use `fun_prop`. Establish `hcL : Continuous fun y : Fin 3 → ℂ => Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i))`. Use `Continuous.matrix_det ?_` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply]`. Use `fin_cases j`. Conclude with `hcA.comp (continuous_apply i)`. Conclude with `hcB.comp (continuous_apply i)`. Conclude with `hcC.comp (continuous_apply i)`.

Establish `hcR : Continuous fun y : Fin 3 → ℂ => 2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0)`. Use `hsd.continuous` as an intermediate fact. Use `fun_prop`. Establish `hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ}`. Use `dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using the standard rewrite rules. Conclude with `congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z`.
-/
theorem sgStar_cube_det_cplx : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  intro Λ hΛ v hv z
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hΛL : Λ = L.lattice.toAddSubgroup := AddSubgroup.ext hL
  have hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L := by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L
  have hwp : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hsd : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hopen : IsOpen ((Λ : Set ℂ)ᶜ) := by
    have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun w => hL w
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w := by
    intro w hw
    rw [colB, hΛ.sqTh_eq hv hw, ← hwp]
    ring
  have hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w := by
    intro w hw
    have hwL : w ∉ L.lattice := fun h => hw ((hL w).2 h)
    have hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      have h1 : DifferentiableAt ℂ L.weierstrassP w :=
        L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
      have h2 := h1.hasDerivAt
      rwa [L.deriv_weierstrassP] at h2
    have hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v) := by
      filter_upwards [hopen.mem_nhds hw] with u hu
      rw [hΛ.sqTh_eq hv hu, hwp]
    have hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v))
        ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) +
          sgStar Λ w ^ 2 * L.derivWeierstrassP w) w :=
      ((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)
    rw [colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]
    push_cast
    ring
  have hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) →
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) =
        2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    intro y hy
    have h := Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2)
      (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))
    rw [← hσ] at h
    rw [Matrix.det_fin_three] at h ⊢
    simp [Matrix.vecHead, Matrix.vecTail] at h ⊢
    rw [hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]
    simp only [colA]
    linear_combination h
  have hcA : Continuous (colA Λ) := by
    have := hsd.continuous
    unfold colA; fun_prop
  have hcB : Continuous (colB Λ v) := by
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colB; fun_prop
  have hcC : Continuous (colC Λ v) := by
    have h1 : Continuous (deriv (sqTh Λ v)) :=
      ((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (sgStar Λ)) := (hsd.contDiff (n := 1)).continuous_deriv le_rfl
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colC; fun_prop
  have hcL : Continuous fun y : Fin 3 → ℂ =>
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    fin_cases j
    · exact hcA.comp (continuous_apply i)
    · exact hcB.comp (continuous_apply i)
    · exact hcC.comp (continuous_apply i)
  have hcR : Continuous fun y : Fin 3 → ℂ =>
      2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    have := hsd.continuous
    fun_prop
  have hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ} := by
    have := dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl
    convert this using 1
    ext y; simp
  exact congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z

end GlobalTheory.FrobStick
