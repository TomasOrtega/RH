import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducing

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

/- English proof (translation)
Use `set A : Matrix (Fin h) (Fin N) (MvPolynomial (Fin N × Fin N) ℚ) := Matrix.of fun p b => C (x (b, Fin.castLE hh p)) with hA`. Use `set B : Matrix (Fin N) (Fin h) (MvPolynomial (Fin N × Fin N) ℚ) := Matrix.of fun b q => X (b, Fin.castLE hh q) with hB`. Establish `hM : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r` using `N) (n := N) (Fin.castLE hh) hh) = (A * B).det := by`. Unfold `initMinor`. Rewrite using `[AlgHom.map_det]`.

Use `congr 1`. Use extensionality with `p q`. Simplify using `[rowAct, Matrix.mul_apply, hA, hB]`. Rewrite using `[hM, PI.IsoDerivBFintype.cauchyBinet]`. Use `Finset.sum_congr rfl fun K _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[← Matrix.det_transpose (A.submatrix id K)]`. Unfold `initMinor`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `p k`. Simplify using `[hA]`.
-/
theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  set A : Matrix (Fin h) (Fin N) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun p b => C (x (b, Fin.castLE hh p)) with hA
  set B : Matrix (Fin N) (Fin h) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun b q => X (b, Fin.castLE hh q) with hB
  have hM : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh)
      = (A * B).det := by
    unfold initMinor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, hA, hB]
  rw [hM, PI.IsoDerivBFintype.cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  · rw [← Matrix.det_transpose (A.submatrix id K)]
    unfold initMinor
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p k
    simp [hA]

/- English proof (translation)
Establish `hwEq : hw ℚ le_rfl (fun r : Fin N => Y.rowLen r) = bideterminant ℚ (r` using `N) (n := N) (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) (fun c => Fin.castLE (colLen_le hY c)) := by`. Rewrite using `[bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) _ (fun c i => rfl), shapeDeg_colLen]`. Rewrite using `[hwEq]`. Unfold `bideterminant`. Rewrite using `[map_prod]`.

Repeatedly rewrite using `[rowAct_leadMinor]`. Rewrite using `[Fintype.prod_sum]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, ← map_prod]`. Both sides reduce to the same expression.
-/
theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hwEq : hw ℚ le_rfl (fun r : Fin N => Y.rowLen r) =
      bideterminant ℚ (r := N) (n := N) (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
        (fun c => Fin.castLE (colLen_le hY c)) := by
    rw [bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) _ (fun c i => rfl), shapeDeg_colLen]
  rw [hwEq]
  unfold bideterminant
  rw [map_prod]
  simp_rw [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod]
  rfl

/- English proof (translation)
Use `set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ`. Establish `hanti : Antitone μ` using `fun a b hab => Y.rowLen_anti a b hab`. Set `L : MvPolynomial (Fin N × Fin N) ℚ →ₗ[ℚ] ℚ` to `{ toFun := fun g => fockQ g h map_add' := fun f f' => (fockQBilin _ f f' h 1).1 map_smul' := fun c f => (fockQBilin _ f 0 h c).2 }`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Use `set z : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun a s : Fin N => x (a, s) with hz`. Establish `hev : eval (idFrame ℚ N N) (rowAct ℚ z h) = eval x h`. Establish `: (eval (idFrame ℚ N N)).comp (rowAct ℚ z).toRingHom = eval x`. Use `MvPolynomial.ringHom_ext (fun a => by simp [rowAct]) fun v => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowAct, aeval_X, eval_X, map_sum, map_mul, eval_C, idFrame]`.

Rewrite using `[Finset.sum_eq_single v.2]`. Simplify using `[hz]`. Introduce `b _ hb`. Simplify using `[Fin.val_inj, hb]`. Simplify using the standard rewrite rules.

Conclude with `congrArg (fun f => f h) this`. Establish `key1 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) = ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, fockQ h (colProd ℚ N Y hY J) * eval x (colProd ℚ N Y hY J)`. Rewrite using `[hz, rowAct_hw_expand, (fockQPos _ _ _).1]`. Express the relevant statement in the definitionally equal form `L _ = _`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[C_mul', L.map_smul, smul_eq_mul, mul_comm]`. Express the relevant statement in the definitionally equal form `fockQ _ h * _ = _`. Rewrite using `[(fockQPos _ _ _).1]`. Establish `key2 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) = eval x h * fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ)`.

Rewrite using `[← fock_space_row_action, (fockQPos _ _ _).1, fock_space_highest_weight N N le_rfl μ hanti _ (dualWeylRowStable ℚ N N μ z h hh), hev]`. Rewrite using `[map_sum, smul_eval]`. Simplify using `only [smul_eval]`. Rewrite using `[← key1, key2, mul_comm]`.
-/
theorem reproducing (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ)
    (hh : h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r)) :
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) •
        GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti a b hab

  let L : MvPolynomial (Fin N × Fin N) ℚ →ₗ[ℚ] ℚ :=
    { toFun := fun g => fockQ g h
      map_add' := fun f f' => (fockQBilin _ f f' h 1).1
      map_smul' := fun c f => (fockQBilin _ f 0 h c).2 }
  apply MvPolynomial.funext
  intro x
  set z : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun a s : Fin N => x (a, s) with hz
  have hev : eval (idFrame ℚ N N) (rowAct ℚ z h) = eval x h := by
    have : (eval (idFrame ℚ N N)).comp (rowAct ℚ z).toRingHom = eval x := by
      refine MvPolynomial.ringHom_ext (fun a => by simp [rowAct]) fun v => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowAct, aeval_X, eval_X,
        map_sum, map_mul, eval_C, idFrame]
      rw [Finset.sum_eq_single v.2]
      · simp [hz]
      · intro b _ hb
        simp [Fin.val_inj, hb]
      · simp
    exact congrArg (fun f => f h) this
  have key1 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, fockQ h (colProd ℚ N Y hY J) * eval x (colProd ℚ N Y hY J) := by
    rw [hz, rowAct_hw_expand, (fockQPos _ _ _).1]
    change L _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [C_mul', L.map_smul, smul_eq_mul, mul_comm]
    change fockQ _ h * _ = _
    rw [(fockQPos _ _ _).1]
  have key2 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) = eval x h * fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ) := by
    rw [← fock_space_row_action, (fockQPos _ _ _).1,
      fock_space_highest_weight N N le_rfl μ hanti _ (dualWeylRowStable ℚ N N μ z h hh), hev]
  rw [map_sum, smul_eval]
  simp only [smul_eval]
  rw [← key1, key2, mul_comm]

end GlobalTheory.WeylReproducing
