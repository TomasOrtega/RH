import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.RouteCoords

section Generic

variable {A : Type} [CommRing A] {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations.
-/
theorem quadruple_sum_eq_trace_transpose_mul (c : A → A) (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) = (x * JB * (y.map c)ᵀ * JAᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem orientedHermitianForm_quadSum_eq_trace (c : A → A) (P : Matrix β β A) (Q : Matrix α α A) (x y : Matrix α β A) :
    ∑ a : β, ∑ b : β, ∑ k : α, ∑ d : α, P a b * c (y k b) * Q k d * x d a = (P * (y.map c)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc (∑ b : β, ∑ k : α, ∑ d : α, P a b * c (y k b) * Q k d * x d a)
      = ∑ b : β, ∑ d : α, ∑ k : α, P a b * c (y k b) * Q k d * x d a :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ d : α, ∑ b : β, ∑ k : α, P a b * c (y k b) * Q k d * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_comm

end Generic

end GlobalTheory.RouteCoords

namespace GlobalTheory.RouteCoords

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

section Block

variable {R : Type} [CommRing R] {n p q d : ℕ}

/- English proof (translation)
Use extensionality with `a s`. Apply the tactic sequence `rcases s with s | s <;> rfl`.
-/
theorem submatrix_eq_fromCols (e : Fin p ⊕ Fin q ≃ Fin d) (x : Matrix (Fin n) (Fin d) R) :
    x.submatrix id e = fromCols (x.submatrix id fun k => e (.inl k)) (x.submatrix id fun k => e (.inr k)) := by
  ext a s
  rcases s with s | s <;> rfl

/- English proof (translation)
Establish `hx : x = (x.submatrix id e).submatrix id e.symm` using `by ext; simp`. Establish `hy : yᵀ = ((y.submatrix id e)ᵀ).submatrix e.symm id` using `by ext; simp`. Use `conv_lhs => rw [hx, hy, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_eq_fromCols, submatrix_eq_fromCols, fromCols_mul_fromBlocks, transpose_fromCols, fromCols_mul_fromRows]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem mul_blk_mul_transpose (e : Fin p ⊕ Fin q ≃ Fin d) (x y : Matrix (Fin n) (Fin d) R)
    (P : Matrix (Fin p) (Fin p) R) (Q : Matrix (Fin q) (Fin q) R) :
    x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q * yᵀ = x.submatrix id (fun k => e (.inl k)) * P * (y.submatrix id fun k => e (.inl k))ᵀ +
      x.submatrix id (fun k => e (.inr k)) * Q * (y.submatrix id fun k => e (.inr k))ᵀ := by
  have hx : x = (x.submatrix id e).submatrix id e.symm := by ext; simp
  have hy : yᵀ = ((y.submatrix id e)ᵀ).submatrix e.symm id := by ext; simp
  conv_lhs => rw [hx, hy, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_eq_fromCols, submatrix_eq_fromCols,
    fromCols_mul_fromBlocks, transpose_fromCols, fromCols_mul_fromRows]
  ext a b
  simp

/- English proof (translation)
Establish `hx : x = (x.submatrix id e).submatrix id e.symm` using `by ext; simp`. Use `conv_lhs => rw [hx, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_eq_fromCols, fromCols_mul_fromBlocks]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem submatrix_mul_blk_inl (e : Fin p ⊕ Fin q ≃ Fin d) (x : Matrix (Fin n) (Fin d) R)
    (P : Matrix (Fin p) (Fin p) R) (Q : Matrix (Fin q) (Fin q) R) :
    (x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).submatrix id (fun k => e (.inl k)) = x.submatrix id (fun k => e (.inl k)) * P := by
  have hx : x = (x.submatrix id e).submatrix id e.symm := by ext; simp
  conv_lhs => rw [hx, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_eq_fromCols, fromCols_mul_fromBlocks]
  ext a b
  simp

/- English proof (translation)
Establish `hx : x = (x.submatrix id e).submatrix id e.symm` using `by ext; simp`. Use `conv_lhs => rw [hx, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_eq_fromCols, fromCols_mul_fromBlocks]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem submatrix_mul_blk_inr (e : Fin p ⊕ Fin q ≃ Fin d) (x : Matrix (Fin n) (Fin d) R)
    (P : Matrix (Fin p) (Fin p) R) (Q : Matrix (Fin q) (Fin q) R) :
    (x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).submatrix id (fun k => e (.inr k)) = x.submatrix id (fun k => e (.inr k)) * Q := by
  have hx : x = (x.submatrix id e).submatrix id e.symm := by ext; simp
  conv_lhs => rw [hx, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_mul_equiv, submatrix_eq_fromCols, fromCols_mul_fromBlocks]
  ext a b
  simp

end Block

section Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Establish `hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0`. Introduce `y`. Rewrite using `[← V.frame.sum_repr y]`.

Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `congrFun h0 i` as an intermediate fact.

Simplify using `only [mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, Pi.zero_apply] at this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by rw [this, mul_zero]`. Use `V.nondeg.2 _ hx` as an intermediate fact.

Conclude with `hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))`.
-/
theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V)), Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem inv_mul_gram (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V)), Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [transpose_apply, map_apply]`. Rewrite using `[GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]`.
-/
theorem gram_conj_transpose (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext a b
  simp only [transpose_apply, map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]

/- English proof (translation)
Rewrite using `[negSp_gram]`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[neg_mul_neg, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]`.
-/
theorem negSp_gram_inv (V : HSp D) : (negSp V).gram⁻¹ = -(V.gram⁻¹) := by
  rw [negSp_gram]
  refine Matrix.inv_eq_left_inv ?_
  rw [neg_mul_neg, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]

/- English proof (translation)
Rewrite using `[GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]`.
-/
theorem adeleConj_incl_skewElement_eq_neg : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]

end Herm

end GlobalTheory.RouteCoords

namespace GlobalTheory.RouteCoords

section Alg

variable {A : Type} [CommRing A] (c : A →+* A) {n a b : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.map_mul, transpose_mul, hg, ← transpose_map, transpose_transpose]`. Rewrite using `[show gi * (g * X'.map c) * q * (Xᵀ * g) = (gi * g) * (X'.map c * q * Xᵀ * g) by simp only [Matrix.mul_assoc], hgi, Matrix.one_mul, ← trace_transpose]`. Simplify using `only [transpose_mul, transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_first (g gi : Matrix (Fin n) (Fin n) A) (q : Matrix (Fin a) (Fin a) A) (hg : (g.map c)ᵀ = g)
    (hgi : gi * g = 1) (X X' : Matrix (Fin n) (Fin a) A) :
    (gi * ((X'ᵀ * g).map c)ᵀ * q * (Xᵀ * g)).trace = (X * qᵀ * (X'.map c)ᵀ * gᵀ).trace := by
  rw [Matrix.map_mul, transpose_mul, hg, ← transpose_map, transpose_transpose]
  rw [show gi * (g * X'.map c) * q * (Xᵀ * g) = (gi * g) * (X'.map c * q * Xᵀ * g) by simp only [Matrix.mul_assoc],
    hgi, Matrix.one_mul, ← trace_transpose]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `cc : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) A), (M.map c).map c = M` using `fun M => by ext; simp [hc]`. Establish `hp' : p.map c = pᵀ` using `by simpa using congrArg transpose hp`. Establish `hg' : g.map c = gᵀ` using `by simpa using congrArg transpose hg`. Establish `e1 : (-(Z'.map c * p)).map c = -(Z' * pᵀ)`. Rewrite using `[Matrix.map_neg _ (map_neg c), Matrix.map_mul, cc, hp']`.

Rewrite using `[e1]`. Establish `e2 : (-pi) * (-(Z' * pᵀ))ᵀ * g * (-(Z.map c * p)) = -((pi * p) * (Z'ᵀ * g * Z.map c * p))`. Simplify using `only [transpose_neg, transpose_mul, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]`. Establish `ct : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) A), c M.trace = (M.map c).trace` using `fun M => by`. Simplify using `[Matrix.trace, map_sum]`.

Rewrite using `[e2, hpi, Matrix.one_mul, trace_neg, mul_neg, map_neg, map_mul, hξ, ct, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, transpose_map, cc, hg', hp', neg_mul, neg_neg]`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[trace_mul_comm Z, show (Z'.map c)ᵀ * (gᵀ * (Z * pᵀ)) = ((Z'.map c)ᵀ * gᵀ * Z) * pᵀ by`. Simplify using `only [Matrix.mul_assoc], trace_mul_comm]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_second (hc : ∀ z, c (c z) = z) (ξ : A) (hξ : c ξ = -ξ) (g : Matrix (Fin n) (Fin n) A)
    (p pi : Matrix (Fin b) (Fin b) A) (hg : (g.map c)ᵀ = g) (hp : (p.map c)ᵀ = p) (hpi : pi * p = 1)
    (Z Z' : Matrix (Fin n) (Fin b) A) :
    c (ξ * ((-pi) * ((-(Z'.map c * p)).map c)ᵀ * g * (-(Z.map c * p))).trace) =
      ξ * (Z * pᵀ * (Z'.map c)ᵀ * gᵀ).trace := by
  have cc : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) A), (M.map c).map c = M := fun M => by ext; simp [hc]
  have hp' : p.map c = pᵀ := by simpa using congrArg transpose hp
  have hg' : g.map c = gᵀ := by simpa using congrArg transpose hg
  have e1 : (-(Z'.map c * p)).map c = -(Z' * pᵀ) := by
    rw [Matrix.map_neg _ (map_neg c), Matrix.map_mul, cc, hp']
  rw [e1]
  have e2 : (-pi) * (-(Z' * pᵀ))ᵀ * g * (-(Z.map c * p)) = -((pi * p) * (Z'ᵀ * g * Z.map c * p)) := by
    simp only [transpose_neg, transpose_mul, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  have ct : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) A), c M.trace = (M.map c).trace := fun M => by
    simp [Matrix.trace, map_sum]
  rw [e2, hpi, Matrix.one_mul, trace_neg, mul_neg, map_neg, map_mul, hξ, ct, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, transpose_map, cc, hg', hp', neg_mul, neg_neg]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm Z, show (Z'.map c)ᵀ * (gᵀ * (Z * pᵀ)) = ((Z'.map c)ᵀ * gᵀ * Z) * pᵀ by
    simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

end Alg

end GlobalTheory.RouteCoords

namespace GlobalTheory.RouteCoords

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

/- English proof (translation)
Rewrite using `[incM_smul, map_neg, map_one, neg_one_smul]`.
-/
theorem incM_neg_one_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    incM ((-1 : D.host.E) • M) = -incM M := by
  rw [incM_smul, map_neg, map_one, neg_one_smul]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J = incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ`. Establish `k : incM Γ.W.J = incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (incM (spV G i j).gramᵀ) (incM (spV₁ G i j).gramᵀ)`. Rewrite using `[hWW, skewGram, incM_smul]`. Use `congr 1`. Conclude with `blk_map _ _ _ (map_zero _)`.

Conclude with `k`. Establish `hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J = -((spW₁ G i j).gram.map (incA D))`. Establish `k : incM Γ.V'.J = -incM (spW₁ G i j).gram` using `by rw [hW₁, incM_neg_one_smul]`. Conclude with `k`. Establish `hA : hTens (R` using `AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ := quadruple_sum_eq_trace …`.

Establish `hB1 : hO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (mulG (spW₁ G i j) (colV e x)ᵀ) (mulG (spW₁ G i j) (colV e x')ᵀ) = _` using `orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spW₁ G i j).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) _ _`. Establish `hB2 : hO (G.pS (.chi i j)) (G.pT (.chi i j)) (adjV₁ e x) (adjV₁ e x') = _` using `orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spV₁ G i j)).gram⁻¹).map (incA D)) ((spW₁ G i j).gram.map (incA D)) _ _`. Unfold `symp symplO`. Rewrite using `[hA, hB1, hB2]`. Use `conv_rhs => arg 2`.

Rewrite using `[← GlobalTheory.DualPairCheck.trace_cA]`. Rewrite using `[← map_add]`. Use `congr 1`. Establish `h1` using `trace_first (cA D) ((spW₁ G i j).gram.map (incA D)) (((spW₁ G i j).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) (gram_conj_transpose _) (inv_mul_gram _) (colV e x) (colV e x')`. Establish `h2` using `trace_second (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) adeleConj_incl_skewElement_eq_neg ((spW₁ G i j).gram.map (incA D)) ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D)) (gram_conj_transpose _) (gram_conj_transpose _) (inv_mul_gram _) (x.su …`.

Rewrite using `[negSp_gram_inv, Matrix.map_neg _ (map_neg _)]`. Establish `hm : ∀ (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)), mulG S y = HMul.hMul y (S.gram.map (incA D))` using `fun _ _ _ => rfl`. Establish `hadj : ∀ y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D), adjV₁ e y = -mulG (spV₁ G i j) ((y.submatrix id fun k => e (.inr k)).map (cA D))` using `fun _ => rfl`. Establish `hcol : ∀ y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D), colV e y = y.submatrix id fun k => e (.inl k)` using `fun _ => rfl`. Simplify using `only [hadj, hm]`.

Simplify using `only [hcol] at h1`. Use `erw [h2, h1]`. Rewrite using `[ hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, mul_blk_mul_transpose, transpose_neg, Matrix.mul_neg, trace_smul, trace_neg, Matrix.add_mul, trace_add, submatrix_map, submatrix_map, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symp_eq (t : T) (e : Num G i j) (Γ : Geo G i j) (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' =
      symplO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (mulG (spW₁ G i j) (colV e x)ᵀ) (mulG (spW₁ G i j) (colV e x')ᵀ) +
      symplO (G.pS (.chi i j)) (G.pT (.chi i j)) (adjV₁ e x) (adjV₁ e x') := by
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (incM (spV G i j).gramᵀ) (incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, skewGram, incM_smul]
      congr 1
      exact blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J = -((spW₁ G i j).gram.map (incA D)) := by
    have k : incM Γ.V'.J = -incM (spW₁ G i j).gram := by rw [hW₁, incM_neg_one_smul]
    exact k
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (mulG (spW₁ G i j) (colV e x)ᵀ) (mulG (spW₁ G i j) (colV e x')ᵀ) = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spW₁ G i j).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO (G.pS (.chi i j)) (G.pT (.chi i j)) (adjV₁ e x) (adjV₁ e x') = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spV₁ G i j)).gram⁻¹).map (incA D)) ((spW₁ G i j).gram.map (incA D)) _ _
  unfold symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add]
  congr 1
  have h1 := trace_first (cA D) ((spW₁ G i j).gram.map (incA D)) (((spW₁ G i j).gram⁻¹).map (incA D))
    ((spV G i j).gram.map (incA D)) (gram_conj_transpose _) (inv_mul_gram _) (colV e x) (colV e x')
  have h2 := trace_second (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) adeleConj_incl_skewElement_eq_neg ((spW₁ G i j).gram.map (incA D))
    ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D)) (gram_conj_transpose _)
    (gram_conj_transpose _) (inv_mul_gram _) (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [negSp_gram_inv, Matrix.map_neg _ (map_neg _)]
  have hm : ∀ (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)), mulG S y = HMul.hMul y (S.gram.map (incA D)) :=
    fun _ _ _ => rfl
  have hadj : ∀ y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      adjV₁ e y = -mulG (spV₁ G i j) ((y.submatrix id fun k => e (.inr k)).map (cA D)) :=
    fun _ => rfl
  have hcol : ∀ y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      colV e y = y.submatrix id fun k => e (.inl k) := fun _ => rfl
  simp only [hadj, hm]
  simp only [hcol] at h1
  erw [h2, h1]
  rw [ hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    mul_blk_mul_transpose, transpose_neg, Matrix.mul_neg, trace_smul, trace_neg, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  ring

end GlobalTheory.RouteCoords

namespace GlobalTheory.RouteCoords

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply]`.
-/
theorem mul_submatrix_cols {R : Type} [CommRing R] {l m n o : Type} [Fintype m] (M : Matrix l m R) (N : Matrix m n R)
    (f : o → n) : (M * N).submatrix id f = M * N.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

end GlobalTheory.RouteCoords

namespace GlobalTheory.RouteCoords

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

/- English proof (translation)
Unfold `mulG colV`. Rewrite using `[← Matrix.add_mul]`. Both sides reduce to the same expression.
-/
theorem mulG_colV_add (e : Num G i j)
    (x w : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    mulG (spW₁ G i j) (colV e (x + w))ᵀ = mulG (spW₁ G i j) (colV e x)ᵀ + mulG (spW₁ G i j) (colV e w)ᵀ := by
  unfold mulG colV
  rw [← Matrix.add_mul]
  rfl

/- English proof (translation)
Unfold `adjV₁ mulG`. Rewrite using `[← neg_add, ← Matrix.add_mul]`. Use `congr 2`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem adjV₁_add (e : Num G i j)
    (x w : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    adjV₁ e (x + w) = adjV₁ e x + adjV₁ e w := by
  unfold adjV₁ mulG
  rw [← neg_add, ← Matrix.add_mul]
  congr 2
  ext a b
  simp

end GlobalTheory.RouteCoords
