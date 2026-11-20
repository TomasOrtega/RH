import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}

/- English proof (translation)
Combine the equalities or inequalities in the calculation `calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm`.
-/
private theorem sum_comm_three_reverse {M ι κ μ : Type*} [AddCommMonoid M] [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → M) : ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k :=
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/- English proof (translation)
Unfold `hO`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `(sum_comm_three_reverse _).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D)).transpose * (T.gram).map (incA D) * x) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (sum_comm_three_reverse _).trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Unfold `halfPair`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem halfPair_eq_trace (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) :
    halfPair W a t = Matrix.trace ((a.map (cA D)).transpose * (W.gram).map (incA D) * t) := by
  unfold halfPair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[GlobalTheory.DualPairCheck.cA_incA]`. Use `congr 1`. Simplify using `only [Matrix.mul_apply, star_sum, star_mul', adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.BesselCompare.sig_eq, star_star, GlobalTheory.DualPairCheck.gram_star]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem map_cA_isoMat_transpose (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Matrix.transpose (((adj D C * V.gram).map (incA D)).map (cA D)) = (V.gram * C).map (incA D) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  congr 1
  simp only [Matrix.mul_apply, star_sum, star_mul', adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    GlobalTheory.BesselCompare.sig_eq, star_star, GlobalTheory.DualPairCheck.gram_star]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Introduce `D V V' W r C B _ K hK a t`. Establish `hG : IsUnit V.gram.det` using `GlobalTheory.LatVac.gram_det_isUnit V`. Establish `h1 : K * V.gram⁻¹ * (V.gram * C) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, hK]`. Establish `key : K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D) = 1`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. It suffices to establish `h : hO V W (restEmb V W K t) (isoPart V W C a) = halfPair W a t by`. Unfold `symplO halfSympl`. Rewrite using `[h]`.

Establish `e1 : (isoPart V W C a).map (cA D) = a.map (cA D) * ((adj D C * V.gram).map (incA D)).map (cA D)`. Unfold `isoPart`. Conclude with `Matrix.map_mul`. Establish `e2 : restEmb V W K t = (t : Matrix (Fin W.rank) (Fin r) (AE D)) * K.map (incA D)` using `rfl`. Rewrite using `[hO_eq_trace, halfPair_eq_trace, e1, Matrix.transpose_mul, map_cA_isoMat_transpose, e2]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm (K.map (incA D))]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [key, Matrix.one_mul]`.
-/
theorem sympl_restEmb_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  intro D V V' W r C B _ K hK a t
  have hG : IsUnit V.gram.det := GlobalTheory.LatVac.gram_det_isUnit V
  have h1 : K * V.gram⁻¹ * (V.gram * C) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, hK]
  have key : K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  suffices h : hO V W (restEmb V W K t) (isoPart V W C a) = halfPair W a t by
    unfold symplO halfSympl
    rw [h]
  have e1 : (isoPart V W C a).map (cA D) = a.map (cA D) * ((adj D C * V.gram).map (incA D)).map (cA D) := by
    unfold isoPart
    exact Matrix.map_mul
  have e2 : restEmb V W K t = (t : Matrix (Fin W.rank) (Fin r) (AE D)) * K.map (incA D) := rfl
  rw [hO_eq_trace, halfPair_eq_trace, e1, Matrix.transpose_mul, map_cA_isoMat_transpose, e2]
  calc _ = Matrix.trace ((K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D)) *
        ((a.map (cA D)).transpose * (W.gram).map (incA D) * t)) := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (K.map (incA D))]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key, Matrix.one_mul]

end GlobalTheory.HalfAverage
