import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GramMatrices.StatementsGramAtPosDef
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.EventuallyInFrameDomain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

/- English proof (translation)
Introduce `τ z c f bfr hz hbfr hdom`. Establish `hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd` using `hz`. Establish `hzP : z ∈ mcPts (mCoordIdeal D.y)` using `hzX.1`. Establish `hex : ∃ l, InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z` using `(D.h τ).cover z hzX`. Establish `hd : InFrameDomain D.y ((D.h τ).chart hex.choose) ((D.h τ).fr hex.choose) z` using `hex.choose_spec`.

Establish `hbAt` using `HermMetricEq.isFrameAt_of_isFrameOver hbfr hzP hdom`. Take `⟨S, hS, hSe⟩` from `HermMetricEq.exists_coeff ((D.h τ).isFrame hex.choose) hzP hd hbAt.1`. Establish `hS' : ∃ S' : Matrix (Fin D.N) (Fin D.N) Ω, ∀ q, bfr q = ∑ p, S' p q • (D.h τ).b hex.choose p` using `⟨S, hSe⟩`. Establish `hchoose : hS'.choose = S` using `HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1 fun q => (hS'.choose_spec q).symm.trans (hSe q)`. Establish `hvals : (Matrix.of fun p q => valAt D.y (hS'.choose p q) z) = HermMetricEq.valM D.y S z`.

Use extensionality with `p q`. Rewrite using `[hchoose]`. Conclude with `valAt_eq hzP (HermMetricEq.isValueAt_iff.2 ((hS p q).isValueAt hzP))`. Establish `hgram : gramAt (D.h τ) bfr z = (HermMetricEq.valM D.y S z)ᴴ * (D.h τ).gram hex.choose z * HermMetricEq.valM D.y S z`. Rewrite using `[gramAt, dif_pos hex, dif_pos hS', hvals]`.

Use `choose U hU hUe using fun q => hbAt.2 _ ((HermMetricEq.isFrameAt_of_isFrameOver ((D.h τ).isFrame hex.choose) hzP hd).1 q)`. Establish `hSU : S * Matrix.of (fun p q => U q p) = 1`. Use `HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1 fun q => ?_` and prove the remaining obligations. Establish `h1 : ∑ p, (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q • (D.h τ).b hex.choose p = (D.h τ).b hex.choose q`. Simplify using `[Matrix.one_apply, ite_smul]`.

Rewrite using `[h1]`. Use `conv_rhs => rw [hUe q]`. Simplify using `only [hSe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Establish `hval : HermMetricEq.valM D.y S z * HermMetricEq.valM D.y (Matrix.of fun p q => U q p) z = 1`. Use extensionality with `p q`. Establish `h1` using `HermMetricEq.isValueAt_mul (Sz := HermMetricEq.valM D.y S z) (Tz := HermMetricEq.valM D.y (Matrix.of fun p q => U q p) z) (fun p q => (hS p q).isValueAt hzP) (fun p q => (hU q p).isValueAt hzP) p q`. Rewrite `h1` using `[hSU]`.

Conclude with `IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hzP h1 (HermMetricEq.isValueAt_one_matrix p q)`. Establish `hinj : Function.Injective (HermMetricEq.valM D.y S z).mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hval))`. Rewrite using `[hgram]`. Conclude with `((D.h τ).posDef hex.choose z hzX hd).conjTranspose_mul_mul_same hinj`.
-/
theorem GramAtPosDef.proof (D : ComponentData II Ψ K ι Ω E) : GramAtPosDef.Statement D := by
  classical
  intro τ z c f bfr hz hbfr hdom
  have hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hzP : z ∈ mcPts (mCoordIdeal D.y) := hzX.1
  have hex : ∃ l, InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z := (D.h τ).cover z hzX
  have hd : InFrameDomain D.y ((D.h τ).chart hex.choose) ((D.h τ).fr hex.choose) z := hex.choose_spec
  have hbAt := HermMetricEq.isFrameAt_of_isFrameOver hbfr hzP hdom
  obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame hex.choose) hzP hd hbAt.1
  have hS' : ∃ S' : Matrix (Fin D.N) (Fin D.N) Ω, ∀ q, bfr q = ∑ p, S' p q • (D.h τ).b hex.choose p :=
    ⟨S, hSe⟩
  have hchoose : hS'.choose = S := HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hSe q)
  have hvals : (Matrix.of fun p q => valAt D.y (hS'.choose p q) z) = HermMetricEq.valM D.y S z := by
    ext p q
    rw [hchoose]
    exact valAt_eq hzP (HermMetricEq.isValueAt_iff.2 ((hS p q).isValueAt hzP))
  have hgram : gramAt (D.h τ) bfr z =
      (HermMetricEq.valM D.y S z)ᴴ * (D.h τ).gram hex.choose z * HermMetricEq.valM D.y S z := by
    rw [gramAt, dif_pos hex, dif_pos hS', hvals]
  choose U hU hUe using fun q =>
    hbAt.2 _ ((HermMetricEq.isFrameAt_of_isFrameOver ((D.h τ).isFrame hex.choose) hzP hd).1 q)
  have hSU : S * Matrix.of (fun p q => U q p) = 1 := by
    refine HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1 fun q => ?_
    have h1 : ∑ p, (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q • (D.h τ).b hex.choose p =
        (D.h τ).b hex.choose q := by
      simp [Matrix.one_apply, ite_smul]
    rw [h1]
    conv_rhs => rw [hUe q]
    simp only [hSe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hval : HermMetricEq.valM D.y S z * HermMetricEq.valM D.y (Matrix.of fun p q => U q p) z = 1 := by
    ext p q
    have h1 := HermMetricEq.isValueAt_mul (Sz := HermMetricEq.valM D.y S z)
      (Tz := HermMetricEq.valM D.y (Matrix.of fun p q => U q p) z)
      (fun p q => (hS p q).isValueAt hzP) (fun p q => (hU q p).isValueAt hzP) p q
    rw [hSU] at h1
    exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hzP h1 (HermMetricEq.isValueAt_one_matrix p q)
  have hinj : Function.Injective (HermMetricEq.valM D.y S z).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hval))
  rw [hgram]
  exact ((D.h τ).posDef hex.choose z hzX hd).conjTranspose_mul_mul_same hinj

end GroundTheory.Heights₂.Heights.LowerBoundFree
