import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceFieldStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

/- English proof (translation)
Establish `hblk` using `GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU`. Consider the cases of `j with`. Consider the case `zero`. Use function extensionality and compare the values at `(v : X.Pl) (s : Fin (X.G.P.n' v))`. Establish `hA : (SecondKernelHermitian.glInv X 0 (SecondKernelHermitian.BOf fd 0 La) v)⁻¹ = SecondKernelHermitian.frGL fd 0 La v` using `inv_inv _`.

Establish `hdet : IsUnit (fd.frM 0 La v).det`. Rewrite using `[hF v, Matrix.det_submatrix_equiv_self]`. Establish `hu` using `((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)`. Rewrite `hu` using `[RingHom.map_det]`. Conclude with `hu`.

Establish `hv : (SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) = fd.frM 0 La v`. Unfold `SecondKernelHermitian.frGL`. Rewrite using `[dif_pos hdet]`. Both sides reduce to the same expression. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `a b`. Establish `e1` using `congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)`. Simplify using `only [Matrix.map_apply] at e1`. Rewrite using `[Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]`. Use `show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) a b))) = _`.

Rewrite using `[hv, hF v]`. Distinguish the cases in `hs : Even s.val`. Establish `ho : ¬ IsOddPos s`. Unfold `IsOddPos`. Rewrite using `[← Nat.odd_iff, ← Nat.not_even_iff_odd]`.

Conclude with `not_not.2 hs`. Rewrite `e1` using `[if_neg ho]`. Simplify using `only [hAt, hs, if_true]`. Rewrite using `[one_mul, inv_one, mul_one]`. Conclude with `e1.symm`.

Establish `ho : IsOddPos s`. Unfold `IsOddPos`. Rewrite using `[← Nat.odd_iff, ← Nat.not_even_iff_odd]`. Conclude with `hs`. Rewrite `e1` using `[if_pos ho]`.

Simplify using `only [hAt, hs, if_false, invT]`. Rewrite using `[one_mul, inv_one, mul_one, ← map_inv]`. Conclude with `e1.symm`. Consider the case `succ j`. Use function extensionality and compare the values at `(v : X.Pl) (s : Fin (X.G.P.n' v))`.

Establish `hA : (SecondKernelHermitian.glInv X (j + 1) (SecondKernelHermitian.BOf fd (j + 1) La) v)⁻¹ = SecondKernelHermitian.frGL fd (j + 1) La v` using `inv_inv _`. Establish `hdet : IsUnit (fd.frM (j + 1) La v).det`. Rewrite using `[hF v, Matrix.det_submatrix_equiv_self]`. Establish `hu` using `((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)`. Rewrite `hu` using `[RingHom.map_det]`.

Conclude with `hu`. Establish `hv : (SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) = fd.frM (j + 1) La v`. Unfold `SecondKernelHermitian.frGL`. Rewrite using `[dif_pos hdet]`. Both sides reduce to the same expression.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Establish `e1` using `congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)`. Simplify using `only [Matrix.map_apply] at e1`. Rewrite using `[Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]`.

Use `show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) a b))) = _`. Rewrite using `[hv, hF v]`. Distinguish the cases in `hs : Even s.val`. Establish `ho : ¬ IsOddPos s`. Unfold `IsOddPos`.

Rewrite using `[← Nat.odd_iff, ← Nat.not_even_iff_odd]`. Conclude with `not_not.2 hs`. Rewrite `e1` using `[if_neg ho]`. Simplify using `only [hAt, hs, if_true]`. Rewrite using `[one_mul, inv_one, mul_one]`.

Conclude with `e1.symm`. Establish `ho : IsOddPos s`. Unfold `IsOddPos`. Rewrite using `[← Nat.odd_iff, ← Nat.not_even_iff_odd]`. Conclude with `hs`.

Rewrite `e1` using `[if_pos ho]`. Simplify using `only [hAt, hs, if_false, invT]`. Rewrite using `[one_mul, inv_one, mul_one, ← map_inv]`. Conclude with `e1.symm`.
-/
theorem blk_frame_eq {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : PosTie X D pos Kc ι ρ) (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n)
    (M : GL (Fin n) D.host.E) (hU : StdU D M) (hF : FrIs fd ρ j La h M) :
    (fun v s => Matrix.GeneralLinearGroup.map (algebraMap X.G.Kf Kc)
        (gPosGL (X.Pj j) v s ((SecondKernelHermitian.glInv X j (SecondKernelHermitian.BOf fd j La) v)⁻¹))) =
      (fun v s => Matrix.GeneralLinearGroup.map ι (hAt (X.Pj j) h (posJ X D pos j) (fun _ => 1) (atR D M) v s)) := by
  have hblk := GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU
  cases j with
  | zero =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X 0 (SecondKernelHermitian.BOf fd 0 La) v)⁻¹ = SecondKernelHermitian.frGL fd 0 La v := inv_inv _
    have hdet : IsUnit (fd.frM 0 La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) = fd.frM 0 La v := by
      unfold SecondKernelHermitian.frGL
      rw [dif_pos hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm
  | succ j =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X (j + 1) (SecondKernelHermitian.BOf fd (j + 1) La) v)⁻¹ = SecondKernelHermitian.frGL fd (j + 1) La v := inv_inv _
    have hdet : IsUnit (fd.frM (j + 1) La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) = fd.frM (j + 1) La v := by
      unfold SecondKernelHermitian.frGL
      rw [dif_pos hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

/- English proof (translation)
Introduce `p _ X D pos Kc _ _ ι ρ hT fd j La n h M hU hF G V hGV`. Unfold `gmOf actC`. Rewrite using `[natAct_eq, map_natActR, map_natActR, ← hGV, blk_frame_eq X D pos Kc ι ρ hT fd j La h M hU hF]`.
-/
theorem gmOf_map_eq_actC : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → ∀ (G : (X.Pj j).Xsp) (V : XR (X.Pj j) ℂ), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι V → MvPolynomial.map (algebraMap X.G.Kf Kc) (gmOf fd j La G) = MvPolynomial.map ι (actC X D pos j h M V) := by
  intro p _ X D pos Kc _ _ ι ρ hT fd j La n h M hU hF G V hGV
  unfold gmOf actC
  rw [natAct_eq, map_natActR, map_natActR, ← hGV, blk_frame_eq X D pos Kc ι ρ hT fd j La h M hU hF]

end GlobalTheory.TwV.DelA
