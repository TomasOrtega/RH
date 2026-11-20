import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

section coef

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1, hF.2.1⟩`.
-/
theorem cptCoef_cont_supp (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) :
    ContinuousOn F (B.GV k r) ∧ ∃ R : ℝ, ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R :=
  ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1, hF.2.1⟩

end coef

section point

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_perm_val {m n : ℕ} (e : m = n) (σ : Equiv.Perm (Fin m)) (x : Fin n) :
    ((e ▸ σ) x).val = (σ (Fin.cast e.symm x)).val := by
  subst e; rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_diag_apply {m n : ℕ} (e : m = n) (d : Fin m → ℂ) (x : Fin n) :
    (e ▸ d) x = d (Fin.cast e.symm x) := by
  subst e; rfl

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hh.2]`.
-/
theorem ptSize_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) : D.ptSize (h ++ [(1, ζ)]) = n + 1 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hh.2]

/- English proof (translation)
Establish `hq : D.IsLocPt (h ++ [(1, ζ)]) (n + 1)` using `Formalism.FourierDecayAlt.P.PBI.isLocPt_app h n hh ζ hζ`. Take `⟨h1, h2⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' h n hh.2 hh.1`. Take `⟨h3, h4⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (h ++ [(1, ζ)]) (n + 1) (ptSize_app h n hh ζ) hq.1`. Use `⟨?_, h2, h3, h4, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Use `(Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ ?_).symm` and prove the remaining obligations. Introduce `a`. Apply `Fin.ext` to reduce the goal to its premises. Establish `e : Fin.cast hh.2.symm ((hh.2 ▸ D.ptPerm h) a) = D.ptPerm h (Fin.cast hh.2.symm a)` using `Fin.ext (by rw [Fin.val_cast, cast_perm_val])`. Rewrite using `[cast_perm_val, e, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol, Fin.val_cast]`.

Introduce `a`. Rewrite using `[Equiv.symm_apply_eq]`. Apply `Fin.ext` to reduce the goal to its premises. Establish `hs` using `hh.2`. Establish `hb` using `((hh.2 ▸ D.ptPerm h) a).isLt`.

Rewrite using `[cast_perm_val, Formalism.FourierDecayAlt.P.Dx1.ptPerm_val, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append 1 ζ h _ (by`. Simplify using `only [Fin.val_cast, Fin.val_castSucc]`. Use the proof step `omega)]`. Rewrite using `[if_pos (by simp only [Fin.val_cast, Fin.val_castSucc]; omega)]`. Simplify using `only [Fin.val_cast, Fin.val_castSucc]`.

Rewrite using `[cast_perm_val]`. Establish `e1` using `Formalism.FourierDecayAlt.P.Dx1.ptPerm_val h (D.ptPerm h (Fin.cast hh.2.symm a))`. Rewrite `e1` using `[Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol]`. Rewrite using `[← e1, Fin.val_cast]`.
-/
theorem perm_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    U.hMat (hh.2 ▸ D.ptPerm h) (hh.2 ▸ D.ptDiag h) = D.ptMatN h n ∧ (∀ a, (hh.2 ▸ D.ptDiag h) a ≠ 0) ∧
    D.ptMatN (h ++ [(1, ζ)]) (n + 1) =
      C2.monoP (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])) (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) ∧
    (∀ a, (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) a ≠ 0) ∧
    (∀ a : Fin n, (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])).symm a.castSucc =
      ((hh.2 ▸ D.ptPerm h) a).castSucc) := by
  have hq : D.IsLocPt (h ++ [(1, ζ)]) (n + 1) := Formalism.FourierDecayAlt.P.PBI.isLocPt_app h n hh ζ hζ
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' h n hh.2 hh.1
  obtain ⟨h3, h4⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (h ++ [(1, ζ)]) (n + 1) (ptSize_app h n hh ζ) hq.1
  refine ⟨?_, h2, h3, h4, ?_⟩
  · rw [h1]
    refine (Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ ?_).symm
    intro a
    apply Fin.ext
    have e : Fin.cast hh.2.symm ((hh.2 ▸ D.ptPerm h) a) = D.ptPerm h (Fin.cast hh.2.symm a) :=
      Fin.ext (by rw [Fin.val_cast, cast_perm_val])
    rw [cast_perm_val, e, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol, Fin.val_cast]
  · intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    have hs := hh.2
    have hb := ((hh.2 ▸ D.ptPerm h) a).isLt
    rw [cast_perm_val, Formalism.FourierDecayAlt.P.Dx1.ptPerm_val, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append 1 ζ h _ (by
      simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    rw [if_pos (by simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    simp only [Fin.val_cast, Fin.val_castSucc]
    rw [cast_perm_val]
    have e1 := Formalism.FourierDecayAlt.P.Dx1.ptPerm_val h (D.ptPerm h (Fin.cast hh.2.symm a))
    rw [Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol] at e1
    rw [← e1, Fin.val_cast]

end point

section frame

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `h : P.r + (P.r - P.r) = P.r` using `by omega`. Establish `e1 : ν'r = Formalism.FourierDecayAlt.P.PBI.nuR p`. Rewrite using `[Formalism.FourierDecayAlt.P.PBI.nuR, ← hν, Formalism.FourierDecayAlt.P.PBI.zL_lift]`. Establish `e2 : m₀r = Formalism.FourierDecayAlt.P.PBI.m0R p`. Use extensionality with `i j`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBI.m0R, ← hm]`. Simplify using `only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]`. Rewrite using `[dif_pos (by simp; omega), dif_pos (by simp; omega)]`. Apply the tactic sequence `congr 1 <;> ext <;> simp`. Rewrite using `[e1, e2]`.

Conclude with `(Formalism.FourierDecayAlt.P.PBI.levFrame_nuR p).2.2`.
-/
theorem baseFrame_last (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    D.IsBaseFrame (p.T.bs P.r) ν'r m₀r := by
  have h : P.r + (P.r - P.r) = P.r := by omega
  have e1 : ν'r = Formalism.FourierDecayAlt.P.PBI.nuR p := by
    rw [Formalism.FourierDecayAlt.P.PBI.nuR, ← hν, Formalism.FourierDecayAlt.P.PBI.zL_lift]
  have e2 : m₀r = Formalism.FourierDecayAlt.P.PBI.m0R p := by
    ext i j
    rw [Formalism.FourierDecayAlt.P.PBI.m0R, ← hm]
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    congr 1 <;> ext <;> simp
  rw [e1, e2]
  exact (Formalism.FourierDecayAlt.P.PBI.levFrame_nuR p).2.2

end frame

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend
