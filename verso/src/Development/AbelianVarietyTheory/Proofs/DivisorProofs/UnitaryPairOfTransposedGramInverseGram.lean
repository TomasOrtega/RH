import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]`. Consider the case `add x y hx hy => simp_all`.
-/
theorem matchPair_cA_eq_sigR (D : D7) (x : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig x = sigR (AF D.host.F) D.sp.cm.sig x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]
  | add x y hx hy => simp_all

/- English proof (translation)
Establish `e1 : Biᵀ * Bmᵀ = 1` using `by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]`. Establish `e2 : P * Cm = Biᵀ * P`. Combine the equalities or inequalities in the displayed calculation. Establish `e3 : Cm * Q = Q * Biᵀ`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem matchPair_inv_transpose {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (Bm Bi P Q Cm Ci : Matrix n n R) (hBB : Bm * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hCC : Ci * Cm = 1) (hb : Bmᵀ * P * Cm = P) : Ci * Q * Biᵀ = Q := by
  have e1 : Biᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  have e2 : P * Cm = Biᵀ * P := by
    calc P * Cm = (Biᵀ * Bmᵀ) * P * Cm := by rw [e1, Matrix.one_mul]
      _ = Biᵀ * (Bmᵀ * P * Cm) := by simp only [Matrix.mul_assoc]
      _ = Biᵀ * P := by rw [hb]
  have e3 : Cm * Q = Q * Biᵀ := by
    calc Cm * Q = (Q * P) * Cm * Q := by rw [hQP, Matrix.one_mul]
      _ = Q * (P * Cm) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ * (P * Q) := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ := by rw [hPQ, Matrix.mul_one]
  calc Ci * Q * Biᵀ = Ci * (Q * Biᵀ) := Matrix.mul_assoc _ _ _
    _ = Ci * (Cm * Q) := by rw [e3]
    _ = Q := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `matchPair_cA_eq_sigR D (M i j)`.
-/
theorem matchPair_map_cA (D : D7) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (AE D)) :
    M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = M.map (sigR (AF D.host.F) D.sp.cm.sig) := by
  ext i j; exact matchPair_cA_eq_sigR D (M i j)

/- English proof (translation)
Establish `ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA` using `a.2`. Use `show Formalism.UG.cT _ _ * _ * _ = _`. Use `congrArg Matrix.transpose ha` as an intermediate fact. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this`. Unfold `Formalism.UG.cT JR`.

Rewrite using `[← matchPair_map_cA]`. Establish `e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]`. Rewrite `this` using `[e]`. Conclude with `(Matrix.mul_assoc _ _ _).trans this`.
-/
theorem matchPair_memT (D : D7) (T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hA : JA = T.gramᵀ)
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) : (a.1 : GL (Fin T.rank) (AE D)) ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  show Formalism.UG.cT _ _ * _ * _ = _
  have := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA]
  have e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  rw [e] at this
  exact (Matrix.mul_assoc _ _ _).trans this

/- English proof (translation)
Establish `hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB` using `b.2`. Establish `hxi : IsUnit (incA D D.host.xi0)` using `(isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _`. Establish `hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D))`. Use extensionality with `i j`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]`.

Establish `t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y)` using `fun r X Y => Matrix.mul_smul X r Y`. Establish `t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y)` using `fun r X Y => Matrix.smul_mul r X Y`. Establish `e1` using `congrArg (fun M => ξ • M) hb`. Rewrite `e1` using `[← t2, ← t1, hB, hsc]`. Establish `e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTenso …`.

Rewrite using `[t1, t2]`. Rewrite `e1` using `[e2]`. Conclude with `hxi.smul_left_cancel.1 e1`.
-/
theorem matchPair_keeps_inv_gram (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F S.gram⁻¹ := by
  have hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB := b.2
  have hxi : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) =
      (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]
  have t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y) :=
    fun r X Y => Matrix.mul_smul X r Y
  have t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y) :=
    fun r X Y => Matrix.smul_mul r X Y
  have e1 := congrArg (fun M => ξ • M) hb
  rw [← t2, ← t1, hB, hsc] at e1
  have e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) := by
    rw [t1, t2]
  rw [e2] at e1
  exact hxi.smul_left_cancel.1 e1

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hBB : b.1.1 * (b⁻¹).1.1 = 1` using `Units.mul_inv b.1`. Establish `hBB' : (b⁻¹).1.1 * b.1.1 = 1` using `Units.inv_mul b.1`. Establish `hdet : IsUnit S.gram.det` using `(Formalism.L2.Theta.gram_det_ne S).isUnit`. Establish `hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1`. Use `map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix : Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1` as an intermediate fact. Rewrite `this` using `[hBB', map_one]`.

Conclude with `this.symm`. Establish `key` using `matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)`. Use `⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one], by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.cT _ _ * _ * _ = _`. Unfold `Formalism.UG.cT JR`.

Rewrite using `[← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]`. Conclude with `key`.
-/
theorem matchPair_memS (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    ∃ G : GL (Fin S.rank) (AE D), G.1 = (b⁻¹).1.1ᵀ ∧ G ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hBB : b.1.1 * (b⁻¹).1.1 = 1 := Units.mul_inv b.1
  have hBB' : (b⁻¹).1.1 * b.1.1 = 1 := Units.inv_mul b.1
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1 := by
    have := map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix :
      Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1
    rw [hBB', map_one] at this
    exact this.symm
  have key := matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)
  refine ⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩
  show Formalism.UG.cT _ _ * _ * _ = _
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]
  exact key

/- English proof (translation)
Introduce `D S T JA JB ξ hA hB a b`. Take `⟨G, hG, hGm⟩` from `matchPair_memS D S JB ξ hB b`. Conclude with `⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩`.
-/
theorem match_pair : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  obtain ⟨G, hG, hGm⟩ := matchPair_memS D S JB ξ hB b
  exact ⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩

end GlobalTheory.WeilSchrodinger

end
