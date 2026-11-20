import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA.ActInv

/- English proof (translation)
Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]`.
-/
theorem det_inv_gl {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = (A : Matrix (Fin n) (Fin n) F).det⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

/- English proof (translation)
Unfold `hAt`. Distinguish the cases in `hs : Even s.val`. Simplify using `only [hs, if_true, one_mul, inv_one, mul_one] show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _`. Unfold `reM`. Rewrite using `[Matrix.det_submatrix_equiv_self]`.

Simplify using `only [hs, if_false, one_mul, inv_one, mul_one] show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _`. Rewrite using `[Matrix.det_transpose, det_inv_gl]`. Use `show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _`. Unfold `reM`. Rewrite using `[Matrix.det_submatrix_equiv_self]`.
-/
theorem det_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((hAt P h pos (fun _ => 1) g v s : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det =
      if Even s.val then (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det
      else (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _
    rw [Matrix.det_transpose, det_inv_gl]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]

/- English proof (translation)
Unfold `hAt`. Distinguish the cases in `hs : Even s.val`. Simplify using `only [hs, if_true, one_mul, inv_one, mul_one]`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Simplify using `only [hs, if_false, one_mul, inv_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem inv_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    (((hAt P h pos (fun _ => 1) g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) =
      if Even s.val then reM P h (((g (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      else Matrix.transpose (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    rw [← map_inv]
    rfl
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.TwV.DelA.ActInv

open GlobalTheory.TwV.DelA.ActInv in

/- English proof (translation)
Introduce `p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R`. Establish `hblk` using `GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU`. Establish `hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A), ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f` using `fun _ _ => rfl`. Establish `hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A), (g.map f).det = f g.det` using `fun f g => (RingHom.map_det f g).symm`. Establish `hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s`.

Introduce `v s`. Unfold `IsOddPos`. Rewrite using `[Nat.even_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) = …`.

Rewrite using `[map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩)` using `by show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)`. Rewrite using `[Equiv.symm_apply_apply]`. Rewrite using `[he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]`.

Rewrite using `[show posJ X D pos (j + 1) = pos from rfl]`. Simplify using `only [atR]`. Rewrite using `[hcoe, hdm, det_inv_gl, map_inv₀]`. Use `split_ifs with h1 h2 h3`. Conclude with `absurd h2 ((hev v s).1 h1)`.

Rewrite using `[map_inv₀, map_zpow₀, inv_zpow', neg_neg]`. Both sides reduce to the same expression. Rewrite using `[inv_inv, map_zpow₀, neg_sub]`. Both sides reduce to the same expression. Conclude with `absurd ((hev v s).2 h3) h1`.

Establish `hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)), ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin (( …`. Introduce `v s a b`. Rewrite using `[← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]`. Establish `hb` using `congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)`. Establish `hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩)` using `by simp [atR, map_inv]`.

Unfold `GlobalTheory.FrameB.mk mAt`. Rewrite using `[Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]`. Rewrite using `[show posJ X D pos (j + 1) = pos from rfl]`. Apply the tactic sequence `split_ifs at hb with h2 <;> split_ifs with h1`. Conclude with `absurd h2 ((hev v s).1 h1)`.

Simplify using `only [Matrix.map_apply, Matrix.transpose_apply] at hb`. Rewrite `hb` using `[hinv]`. Conclude with `hb`. Simplify using `only [Matrix.map_apply] at hb`. Establish `e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩)` using `by rw [← hinv, inv_inv]`.

Use `Eq.trans ?_ hb` and prove the remaining obligations. Conclude with `congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)`. Conclude with `absurd ((hev v s).2 h2) h1`. Establish `hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j ( …`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce and unpack `⟨v, s, a, t⟩`. Simplify using `only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]`. Use `Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_` and prove the remaining obligations. Rewrite using `[hent v s a b]`. Use `congr 2`.

Unfold `actC`. Rewrite using `[map_natActR]`. Unfold `natActR`. Rewrite using `[LinearMap.smul_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[hsc, hsub]`.
-/
theorem GlobalTheory.TwV.DelA.actC_inv_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R
  have hblk := GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  have hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A),
      ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f :=
    fun _ _ => rfl
  have hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A),
      (g.map f).det = f g.det := fun f g => (RingHom.map_det f g).symm
  have hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s := by
    intro v s; unfold IsOddPos; rw [Nat.even_iff]; omega
  have hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) =
      ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) := by
    rw [map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    have he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩) := by
      show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)
      rw [Equiv.symm_apply_apply]
    rw [he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    simp only [atR]
    rw [hcoe, hdm, det_inv_gl, map_inv₀]
    split_ifs with h1 h2 h3
    · exact absurd h2 ((hev v s).1 h1)
    · rw [map_inv₀, map_zpow₀, inv_zpow', neg_neg]
      rfl
    · rw [inv_inv, map_zpow₀, neg_sub]
      rfl
    · exact absurd ((hev v s).2 h3) h1
  have hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)),
      ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc) a b =
      GlobalTheory.FrameB.mk Kc fd j La' v s (Fin.cast (rankJ X (j + 1)) a) (Fin.cast (rankJ X (j + 1)) b) := by
    intro v s a b
    rw [← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]
    have hb := congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)
    have hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩) := by simp [atR, map_inv]
    unfold GlobalTheory.FrameB.mk mAt
    rw [Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    split_ifs at hb with h2 <;> split_ifs with h1
    · exact absurd h2 ((hev v s).1 h1)
    · simp only [Matrix.map_apply, Matrix.transpose_apply] at hb
      rw [hinv] at hb
      exact hb
    · simp only [Matrix.map_apply] at hb
      have e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩) := by rw [← hinv, inv_inv]
      refine Eq.trans ?_ hb
      exact congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)
    · exact absurd ((hev v s).2 h2) h1
  have hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]
    refine Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_
    rw [hent v s a b]
    congr 2
  unfold actC
  rw [map_natActR]
  unfold natActR
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hsc, hsub]
