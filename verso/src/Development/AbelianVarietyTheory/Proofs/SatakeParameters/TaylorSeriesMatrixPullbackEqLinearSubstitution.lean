import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorDirLinear
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

/- English proof (translation)
Use function extensionality and compare the values at `z`. Unfold `TaylorLogMetric.pull`. Use `congr 1`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT, Fintype.sum_prod_type, pullMat]`.

Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]`. Simplify using `only [if_true]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[← Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pull_eq_linear (D : D7) (T : TaylorLogMetric.Tor D) (hT : ∀ τ, T.emb τ = TaylorLogMetric.embT D τ) {a b : ℕ}
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.pull D T e e' Θ = fun z => Θ (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin b × Fin a, pullMat e e' (τ, i, j) x * z x.1 x.2.1 x.2.2) := by
  funext z
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT,
    Fintype.sum_prod_type, pullMat]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.star_def]
  ring

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

/- English proof (translation)
Use extensionality with `α`. Conclude with `GlobalTheory.ConjSeries.taylor_eq_coeff D G α`.
-/
theorem tay_eq_taylorDir (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) :
    tay G = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
  ext α
  exact GlobalTheory.ConjSeries.taylor_eq_coeff D G α

/- English proof (translation)
Introduce `D cc δ a b e e' Θ hΘ`. Rewrite using `[pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]`. Conclude with `GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ`.
-/
theorem tay_pull_linSub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  intro D cc δ a b e e' Θ hΘ
  rw [pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]
  exact GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ

end GlobalTheory.TwV.DelB
