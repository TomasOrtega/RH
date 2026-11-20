import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Sympl

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_sum_eq_trace {A : Type} [CommRing A] {m n : ℕ} (H : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * y c b * G c d * x d a = Matrix.trace (H * (yᵀ * (G * x))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Matrix.transpose_mul]`. Establish `hre : H * (Q'ᵀ * yᵀ * (G * (x * Q))) = (H * Q'ᵀ * yᵀ * G * x) * Q`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hre, Matrix.trace_mul_comm (H * Q'ᵀ * yᵀ * G * x) Q]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_change {A : Type} [CommRing A] {m n : ℕ} (H Q Q' : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((Q * (H * Q'ᵀ)) * (yᵀ * (G * x))) = Matrix.trace (H * ((y * Q')ᵀ * (G * (x * Q)))) := by
  rw [Matrix.transpose_mul]
  have hre : H * (Q'ᵀ * yᵀ * (G * (x * Q))) = (H * Q'ᵀ * yᵀ * G * x) * Q := by
    simp only [Matrix.mul_assoc]
  rw [hre, Matrix.trace_mul_comm (H * Q'ᵀ * yᵀ * G * x) Q]
  simp only [Matrix.mul_assoc]

variable {D : D7}

/- English proof (translation)
Establish `hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l` using `fun k => by`. Simplify using `only [frP, Module.Basis.toMatrix_apply]`. Conclude with `(S.frame.sum_repr (b k)).symm`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `S.hT (b i) (b j) = _`.

Rewrite using `[hb i, hb j]`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Simplify using `only [HSpace.gram, RingHom.id_apply, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))
      = (frP S b)ᴴ * HSpace.gram S * frP S b := by
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    simp only [frP, Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  ext i j
  change S.hT (b i) (b j) = _
  rw [hb i, hb j]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  simp only [HSpace.gram, RingHom.id_apply, starRingEnd_apply]
  ring

/- English proof (translation)
Establish `h` using `gram_reS S b`. Simplify using `only at h ⊢`. Rewrite using `[h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv, Matrix.inv_eq_left_inv (frPinv_mul_frP S b)]`.
-/
theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))⁻¹
      = frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ) := by
  have h := gram_reS S b
  dsimp only at h ⊢
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_eq_left_inv (frPinv_mul_frP S b)]

/- English proof (translation)
Unfold `hO`. Simplify using `only`. Use `Eq.trans ?_ (quad_sum_eq_trace _ _ _ _)` and prove the remaining obligations. Simplify using `only [Matrix.map_apply]`.
-/
theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (((HSpace.gram S)⁻¹).map (incA D) *
      ((Matrix.map (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from y) (cA D))ᵀ *
        ((HSpace.gram T).map (incA D) * (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x)))) := by
  unfold hO
  dsimp only
  refine Eq.trans ?_ (quad_sum_eq_trace _ _ _ _)
  simp only [Matrix.map_apply]

/- English proof (translation)
Establish `hP : (frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ)).map (incA D) = (frPinv S b).map (incA D) * ((HSpace.gram S)⁻¹.map (incA D) * (((frPinv S b).map (incA D)).map (cA D))ᵀ)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Establish `hi` using `gram_reS_inv S b`. Simplify using `only at hi`.

Establish `key` using `trace_change ((HSpace.gram S)⁻¹.map (incA D)) ((frPinv S b).map (incA D)) (((frPinv S b).map (incA D)).map (cA D)) ((HSpace.gram T).map (incA D)) x (y.map (cA D))`. Rewrite `key` using `[← hP, ← hi]`. Rewrite using `[hO_eq_trace, hO_eq_trace]`. Simplify using `only`. Use `key.trans ?_` and prove the remaining obligations.

Use `clear key hi hP`. Unfold `reW`. Establish `hm : (HMul.hMul (α` using `Matrix (Fin T.rank) (Fin S.rank) (AE D)) y ((frPinv S b).map (incA D))).map (cA D) = Matrix.map (α := AE D) (m := Fin T.rank) (n := Fin S.rank) y (cA D) * ((frPinv S b).map (incA D)).map (cA D) := Matrix.map_mul`. Conclude with `congrArg (fun M => ((HSpace.gram S)⁻¹.map (incA D) * (Mᵀ * ((HSpace.gram T).map (incA D) * HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))))).trace) hm.symm`.
-/
theorem hO_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T) :
    hO (reS S b) T x y = hO S T (reW S T b x) (reW S T b y) := by
  have hP : (frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ)).map (incA D) =
      (frPinv S b).map (incA D) * ((HSpace.gram S)⁻¹.map (incA D) *
        (((frPinv S b).map (incA D)).map (cA D))ᵀ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
  have hi := gram_reS_inv S b
  dsimp only at hi
  have key := trace_change ((HSpace.gram S)⁻¹.map (incA D)) ((frPinv S b).map (incA D))
    (((frPinv S b).map (incA D)).map (cA D)) ((HSpace.gram T).map (incA D)) x (y.map (cA D))
  rw [← hP, ← hi] at key
  rw [hO_eq_trace, hO_eq_trace]
  dsimp only
  refine key.trans ?_
  clear key hi hP
  unfold reW
  have hm : (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) y ((frPinv S b).map (incA D))).map (cA D) =
      Matrix.map (α := AE D) (m := Fin T.rank) (n := Fin S.rank) y (cA D) * ((frPinv S b).map (incA D)).map (cA D) :=
    Matrix.map_mul
  exact congrArg (fun M => ((HSpace.gram S)⁻¹.map (incA D) *
    (Mᵀ * ((HSpace.gram T).map (incA D) *
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))))).trace) hm.symm

/- English proof (translation)
Introduce `D S T b x y`. Unfold `symplO`. Rewrite using `[hO_reW]`.
-/
theorem symplO_reW : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T),
    symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  intro D S T b x y
  unfold symplO
  rw [hO_reW]

end GlobalTheory.AdSpan.ReVec.Sympl

end
