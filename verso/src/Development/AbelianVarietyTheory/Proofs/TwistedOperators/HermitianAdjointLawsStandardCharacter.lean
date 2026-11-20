import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAlg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.AdjLawPf

variable {D : D7}

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)`.
-/
theorem inv_mul_gram (V : HSp D) : ((HSpace.gram V)⁻¹.map (incA D)) * ((HSpace.gram V).map (incA D)) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)

/- English proof (translation)
The claim follows from `GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)`.
-/
theorem gramI_conj (V : HSp D) : (((HSpace.gram V)⁻¹.map (incA D)).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) :=
  GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem conjT_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (B : Matrix (Fin n) (Fin k) (AE D)) :
    ((A * B).map (cA D))ᵀ = (B.map (cA D))ᵀ * (A.map (cA D))ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GlobalTheory.DualPairCheck.cA_cA]`.
-/
theorem conjT_conjT {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) : (((A.map (cA D))ᵀ).map (cA D))ᵀ = A := by
  ext i j; simp [GlobalTheory.DualPairCheck.cA_cA]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adjO_eq (S T : HSp D) (y : WO T S) :
    (adjO S T y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      HMul.hMul (HMul.hMul ((HSpace.gram T)⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose) ((HSpace.gram S).map (incA D)) := rfl

/- English proof (translation)
Rewrite using `[adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]`.
-/
theorem adj_invol (S T : HSp D) (x : WO S T) : adjO S T (adjO T S x) = x := by
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]
  simp only [← Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[adjO_eq, adjO_eq, adjO_eq]`. Establish `e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) = (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]`.
-/
theorem adj_add (S T : HSp D) (y y' : WO T S) : adjO S T (y + y') = adjO S T y + adjO S T y' := by
  rw [adjO_eq, adjO_eq, adjO_eq]
  have e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) =
      (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) := by
    ext i j; simp
  rw [e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Rewrite using `[adjO_eq]`. Simplify using `only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_comm`.
-/
theorem hO_eq (S T : HSp D) (x y : WO S T) : hO S T x y = Matrix.trace (adjO T S y * x) := by
  rw [adjO_eq]
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

/- English proof (translation)
Rewrite using `[hO_eq, hO_eq]`. Establish `e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ)`. Rewrite using `[Matrix.trace_transpose]`. Simplify using `only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]`. Rewrite using `[e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj, adjO_eq, Matrix.trace_mul_comm]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  rw [hO_eq, hO_eq]
  have e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ) := by
    rw [Matrix.trace_transpose]; simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
  rw [e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj,
    adjO_eq, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]`.
-/
theorem hO_adj (S T : HSp D) (x y : WO T S) : hO S T (adjO S T x) (adjO S T y) = hO T S y x := by
  rw [hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]

/- English proof (translation)
Unfold `symplO`. Rewrite using `[hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]`.
-/
theorem adj_sympl (S T : HSp D) (y y' : WO T S) :
    symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y' := by
  unfold symplO
  rw [hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[adj_sympl, mul_neg]`.
-/
theorem symplOH_adj (S T : HSp D) (y y' : WO T S) :
    symplOH S T (adjO S T y) (adjO S T y') = -symplOH T S y y' := by
  unfold symplOH; rw [adj_sympl, mul_neg]

end GlobalTheory.AdjLawPf

namespace GlobalTheory.AdjLawPf

variable {D : D7}

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Rewrite using `[← mt_mul, mul_inv_cancel, mt_one]`.
-/
theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

/- English proof (translation)
Rewrite using `[← mt_mul, inv_mul_cancel, mt_one]`.
-/
theorem mt_inv_mul (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mt_mul_inv, Matrix.mul_one]`. Use `_ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]`.
-/
theorem conjT_gram (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V g⁻¹ := by
  calc ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * (mt V g * mt V g⁻¹) := by
        rw [mt_mul_inv, Matrix.mul_one]
    _ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]

/- English proof (translation)
Establish `k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h`. Rewrite using `[conjT_gram, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]`. Use `_ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]`.
-/
theorem gramI_conjT (V : HSp D) (h : GA D V) :
    ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = mt V h * ((HSpace.gram V)⁻¹.map (incA D)) := by
  have k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h := by
    rw [conjT_gram, inv_inv]
  calc ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ * (((HSpace.gram V).map (incA D)) * ((HSpace.gram V)⁻¹.map (incA D))) := by
        rw [GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]
    _ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

/- English proof (translation)
Unfold `actO`. Rewrite using `[adjO_eq, adjO_eq, conjT_mul, conjT_mul]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem adj_act (S T : HSp D) (g : GA D S) (h : GA D T) (y : WO T S) :
    adjO S T (actO T S h g y) = actO S T g h (adjO S T y) := by
  unfold actO
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul]
  simp only [← Matrix.mul_assoc]
  rw [gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D)`. Use extensionality with `i j`. Simplify using `[GlobalTheory.DualPairCheck.cA_incA]`. Rewrite using `[adjO_eq]`. Unfold `ratW`.

Rewrite using `[e, Matrix.map_mul, Matrix.map_mul]`.
-/
theorem adj_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjO S T (ratW S T γ) = ratW T S (HMul.hMul (HMul.hMul (HSpace.gram T)⁻¹ (γ.map star)ᵀ) (HSpace.gram S)) := by
  have e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D) := by
    ext i j; simp [GlobalTheory.DualPairCheck.cA_incA]
  rw [adjO_eq]
  unfold ratW
  rw [e, Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Take `⟨γ, rfl⟩` from `hy`. Conclude with `⟨_, (adj_ratW S T γ).symm⟩`.
-/
theorem adj_rat_of (S T : HSp D) (y : WO T S) (hy : y ∈ ratL S T) : adjO S T y ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨_, (adj_ratW S T γ).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩`.
-/
theorem adj_rat (S T : HSp D) (y : WO T S) : adjO S T y ∈ ratL T S ↔ y ∈ ratL S T :=
  ⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩

/- English proof (translation)
Introduce `i j`. Establish `hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l)` using `fun k l => by rw [← map_mul, hy]`. Rewrite using `[adjO_eq]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Take the linear combination `(incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l`.
-/
theorem adj_half (S T : HSp D) (e : AE D) (y : WO T S) (hy : IsHalf e y) : IsHalf (cA D e) (adjO S T y) := by
  intro i j
  have hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy]
  rw [adjO_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ` using `(continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose`. Conclude with `(continuous_const.matrix_mul h).matrix_mul continuous_const`.
-/
theorem adj_cont (S T : HSp D) : Continuous (adjO S T) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ :=
    (continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Establish `h0 : ∀ k l, infPart D (u k l) = 0` using `fun k l => by`. Use `congrFun (congrFun hu k) l` as an intermediate fact. Simplify `this` using `only [Matrix.map_apply, Matrix.zero_apply]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `show infPart D (adjO S T u i j) = 0`.

Simplify using `only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]`.
-/
theorem adj_infPart (S T : HSp D) (u : WO T S) (hu : u.map (infPart D) = 0) : (adjO S T u).map (infPart D) = 0 := by
  have h0 : ∀ k l, infPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show infPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Establish `h0 : ∀ k l, finPart D (u k l) = 0` using `fun k l => by`. Use `congrFun (congrFun hu k) l` as an intermediate fact. Simplify `this` using `only [Matrix.map_apply, Matrix.zero_apply]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `show finPart D (adjO S T u i j) = 0`.

Simplify using `only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]`.
-/
theorem adj_finPart (S T : HSp D) (u : WO T S) (hu : u.map (finPart D) = 0) : (adjO S T u).map (finPart D) = 0 := by
  have h0 : ∀ k l, finPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show finPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def adjHom (S T : HSp D) : WO T S →+ WO S T := AddMonoidHom.mk' (adjO S T) (adj_add S T)

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]`. Simplify using the standard rewrite rules.
-/
theorem conj_psi (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]`.
-/
theorem adj_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (y : WO T S) (f : WO S T → ℂ) :
    heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f) := by
  funext w
  simp only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]

/- English proof (translation)
Simplify using `only [dag]`. Rewrite using `[adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]`. Simplify using `only [neg_neg]`. Use `level := by`. Take `⟨U, hUo, hU⟩` from `hf.level`.

Use `⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[adj_heis ψ hψ]`. Conclude with `congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))`. Use `cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))`. Use `smooth k L hL hfin w := by`.

Establish `h` using `hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t)) (adjO S T w)`. Establish `e : (fun t => dag S T f (w + L t)) = fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t))`. Use function extensionality and compare the values at `t`. Simplify using `[dag, adj_add, adjHom]`. Rewrite using `[e]`.

Conclude with `Complex.conjCLE.contDiff.comp h`.
-/
theorem adj_theta (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (dag S T f) where
  quasi γ w := by
    simp only [dag]
    rw [adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]
    simp only [neg_neg]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩
    rw [adj_heis ψ hψ]
    exact congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))
  cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t))
      (adjO S T w)
    have e : (fun t => dag S T f (w + L t)) =
        fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t)) := by
      funext t; simp [dag, adj_add, adjHom]
    rw [e]
    exact Complex.conjCLE.contDiff.comp h

/- English proof (translation)
Introduce `D ψ hψ S T`. Establish `hn : ∀ x, ‖ψ x‖ = 1` using `hψ.1.2.1`. Conclude with `{ invol := adj_invol S T add := adj_add S T cont := adj_cont S T sympl := adj_sympl S T act := adj_act S T rat := adj_rat S T half := adj_half S T Heisenberg₂ := adj_heis ψ hn S T theta := adj_theta ψ hn S T }`.
-/
theorem adjLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  intro D ψ hψ S T
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  exact { invol := adj_invol S T
          add := adj_add S T
          cont := adj_cont S T
          sympl := adj_sympl S T
          act := adj_act S T
          rat := adj_rat S T
          half := adj_half S T
          Heisenberg₂ := adj_heis ψ hn S T
          theta := adj_theta ψ hn S T }

end GlobalTheory.AdjLawPf
