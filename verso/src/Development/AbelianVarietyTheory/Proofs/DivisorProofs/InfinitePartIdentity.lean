import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula

open Matrix NumberField
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.QuotientNormCoisometry

/- English proof (translation)
Rewrite using `[← diagonal_one, l2_opNorm_diagonal]`. Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp`.
-/
theorem norm_one_le {k : ℕ} : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

/- English proof (translation)
Establish `hWt : ‖Wᴴ‖ ≤ 1`. Establish `h1 : ‖Wᴴ‖ * ‖Wᴴ‖ = ‖W * Wᴴ‖`. Rewrite using `[← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose]`. Rewrite `h1` using `[hW]`. Use polynomial arithmetic with `[norm_nonneg Wᴴ, norm_one_le (k := k)]`.

Establish `hW1 : ‖W‖ ≤ 1` using `by rwa [l2_opNorm_conjTranspose] at hWt`. Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_mul_coisom {m k l : ℕ} (T : Matrix (Fin m) (Fin k) ℂ) (W : Matrix (Fin k) (Fin l) ℂ)
    (hW : W * Wᴴ = 1) : ‖T * W‖ = ‖T‖ := by
  have hWt : ‖Wᴴ‖ ≤ 1 := by
    have h1 : ‖Wᴴ‖ * ‖Wᴴ‖ = ‖W * Wᴴ‖ := by
      rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose]
    rw [hW] at h1
    nlinarith [norm_nonneg Wᴴ, norm_one_le (k := k)]
  have hW1 : ‖W‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose] at hWt
  apply le_antisymm
  · calc ‖T * W‖ ≤ ‖T‖ * ‖W‖ := l2_opNorm_mul _ _
      _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg _) hW1
  · calc ‖T‖ = ‖T * W * Wᴴ‖ := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]
      _ ≤ ‖T * W‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
      _ ≤ ‖T * W‖ := mul_le_of_le_one_right (norm_nonneg _) hWt

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hY, conjTranspose_nonsing_inv, nonsing_inv_nonsing_inv _ (by rw [det_conjTranspose]; exact hY.star)]`.
-/
theorem inv_met {k : ℕ} (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsUnit Y.det) :
    ((Y⁻¹)ᴴ * Y⁻¹)⁻¹ = Y * Yᴴ := by
  rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hY, conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ (by rw [det_conjTranspose]; exact hY.star)]

/- English proof (translation)
Establish `hA : A⁻¹ = X * Xᴴ` using `by rw [← hX.2, inv_met X hX.1]`. Establish `hQinv : IsUnit (XQ⁻¹).det` using `isUnit_nonsing_inv_det XQ hQ.1`. Establish `hBu : IsUnit (P * A⁻¹ * Pᴴ).det`. Rewrite using `[← isUnit_nonsing_inv_det_iff, ← hQ.2, det_mul, det_conjTranspose]`. Conclude with `hQinv.star.mul hQinv`.

Establish `hB : P * A⁻¹ * Pᴴ = XQ * XQᴴ`. Rewrite using `[← nonsing_inv_nonsing_inv _ hBu, ← hQ.2, inv_met XQ hQ.1]`. Establish `hW : (XQ⁻¹ * P * X) * (XQ⁻¹ * P * X)ᴴ = 1`. Rewrite using `[conjTranspose_mul, conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = XQ⁻¹ * (XQ * XQᴴ) * (XQ⁻¹)ᴴ := by rw [← hA, hB]`. Use `_ = (XQ⁻¹ * XQ) * (XQᴴ * (XQ⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[nonsing_inv_mul _ hQ.1, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hQ.1, conjTranspose_one]`.

Establish `e : Y * (V * P) * X = (Y * V * XQ) * (XQ⁻¹ * P * X)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_nonsing_inv _ hQ.1]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Rewrite using `[e, norm_mul_coisom _ _ hW]`.
-/
theorem norm_quot {n d D : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin D) (Fin n) ℂ)
    (XQ : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (hQ : IsUnit XQ.det ∧ (XQ⁻¹)ᴴ * XQ⁻¹ = (P * A⁻¹ * Pᴴ)⁻¹) (hX : IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = A)
    (V : Matrix (Fin d) (Fin D) ℂ) : ‖Y * V * XQ‖ = ‖Y * (V * P) * X‖ := by
  have hA : A⁻¹ = X * Xᴴ := by rw [← hX.2, inv_met X hX.1]
  have hQinv : IsUnit (XQ⁻¹).det := isUnit_nonsing_inv_det XQ hQ.1
  have hBu : IsUnit (P * A⁻¹ * Pᴴ).det := by
    rw [← isUnit_nonsing_inv_det_iff, ← hQ.2, det_mul, det_conjTranspose]
    exact hQinv.star.mul hQinv
  have hB : P * A⁻¹ * Pᴴ = XQ * XQᴴ := by
    rw [← nonsing_inv_nonsing_inv _ hBu, ← hQ.2, inv_met XQ hQ.1]
  have hW : (XQ⁻¹ * P * X) * (XQ⁻¹ * P * X)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc XQ⁻¹ * P * X * (Xᴴ * (Pᴴ * (XQ⁻¹)ᴴ)) = XQ⁻¹ * (P * (X * Xᴴ) * Pᴴ) * (XQ⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = XQ⁻¹ * (XQ * XQᴴ) * (XQ⁻¹)ᴴ := by rw [← hA, hB]
      _ = (XQ⁻¹ * XQ) * (XQᴴ * (XQ⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nonsing_inv_mul _ hQ.1, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hQ.1, conjTranspose_one]
  have e : Y * (V * P) * X = (Y * V * XQ) * (XQ⁻¹ * P * X) := by
    calc Y * (V * P) * X = Y * V * (XQ * XQ⁻¹) * P * X := by
          rw [mul_nonsing_inv _ hQ.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, norm_mul_coisom _ _ hW]

/- English proof (translation)
Unfold `Formalism.HN.htMap`. Use `congr 1`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Unfold `Formalism.HN.opNormAt`. Establish `hm : ∀ {a b : ℕ} (M : Matrix (Fin b) (Fin a) K), LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) M.mulVecLin = M` using `fun M => by`.

Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hm, hm]`. Establish `e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ), ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ = ‖M‖` using `fun M => (l2_opNorm_def M).symm`. Rewrite using `[e, e, Matrix.map_mul, norm_quot (H.map v.embedding) (P.map v.embedding) (XQ v) (X v) (X' v)⁻¹ (hQ v) (hX v)]`.
-/
theorem htMap_quot {K : Type} [Field K] [NumberField K] [StarRing K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hQ : Formalism.DivisionValues.IsQuotMetric P H XQ)
    (hX : ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (vb : Matrix (Fin d) (Fin D) K) :
    Formalism.HN.htMap (Pi.basisFun K (Fin D)) XQ (Pi.basisFun K (Fin d)) X' vb.mulVecLin =
      Formalism.HN.htMap (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin d)) X' (vb * P).mulVecLin := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Formalism.HN.opNormAt
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin b) (Fin a) K),
      LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) M.mulVecLin = M := fun M => by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hm, hm]
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ),
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ = ‖M‖ := fun M => (l2_opNorm_def M).symm
  rw [e, e, Matrix.map_mul, norm_quot (H.map v.embedding) (P.map v.embedding) (XQ v) (X v) (X' v)⁻¹ (hQ v) (hX v)]

section Bound

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

/- English proof (translation)
Establish `hS` using `LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.sig_le d ∅ (fun _ => 0) hC`. Establish `hN` using `GlobalTheory.BigTop.Fun.Model.N_eq d`. Unfold `FunData.bIPa aOne`. Rewrite using `[hN]`. Use `show (D.R.m : ℝ) * (C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b + C * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * sig d.G) ≤ C * D.R.f * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b + C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid …`.

Establish `h0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hS h0]`.
-/
theorem bound_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) :
    (D.R.m : ℝ) * aOne d.G C p.Z.b ≤ d.O.bIPa C p.Z.b := by
  have hS := LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.sig_le d ∅ (fun _ => 0) hC
  have hN := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bIPa aOne
  rw [hN]
  show (D.R.m : ℝ) * (C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * sig d.G) ≤
    C * D.R.f * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * (d.data (fun _ => 1) ∅ fun _ => 0).Sig0 C p.Z.b
  have h0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS h0]

end Bound

open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize in

/- English proof (translation)
Introduce `hB hS hI`. Take `⟨CF0, hI⟩` from `hI`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, hI⟩` from `hI CF hCF`. Take `⟨e1, he1, hS⟩` from `hS`.

Use `⟨e1, he1, fun eps h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hS eps h1 h2`. Use `⟨K, fun Fm CH hc hL _ => ?_⟩` and prove the remaining obligations. Take `⟨x1, hx1⟩` from `hK Fm CH hc hL`. Use `⟨max C0 (max CF 0), fun C hC => ?_⟩` and prove the remaining obligations.

Establish `hCF' : CF ≤ C` using `((le_max_left _ _).trans (le_max_right _ _)).trans hC`. Establish `hC0 : 0 ≤ C` using `((le_max_right _ _).trans (le_max_right _ _)).trans hC`. Take `⟨x0, hx0⟩` from `hI eps C (le_of_max_le_left hC)`. Use `⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩` and prove the remaining obligations. Take `⟨-, a, ha⟩` from `hd`.

Establish `hset` using `hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser`. Establish `key` using `hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset a.ch ha.ok.is a.atScale ha.ok.field`. Establish `hWF` using `(hB p hp).1`. Establish `hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL, IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧ ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ * (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.f …` using `fun v => Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)`. Establish `k3` using `key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')`.

Rewrite using `[htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]`. Conclude with `k3.trans (bound_le d hC0 hCF')`.
-/
theorem ipa_tie : Bundle → SetAt → InfK → IPa @Comparison₂ := by
  intro hB hS hI
  obtain ⟨CF0, hI⟩ := hI
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hI⟩ := hI CF hCF
  obtain ⟨e1, he1, hS⟩ := hS
  refine ⟨e1, he1, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := hS eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨x1, hx1⟩ := hK Fm CH hc hL
  refine ⟨max C0 (max CF 0), fun C hC => ?_⟩
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x0, hx0⟩ := hI eps C (le_of_max_le_left hC)
  refine ⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hset := hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser
  have key := hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset
    a.ch ha.ok.is a.atScale ha.ok.field
  have hWF := (hB p hp).1
  have hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL,
      IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧
      ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ *
        (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹ =
        ((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding := fun v =>
    Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)
  have k3 := key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')
  rw [htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]
  exact k3.trans (bound_le d hC0 hCF')

end GlobalTheory.QuotientNormCoisometry

end
