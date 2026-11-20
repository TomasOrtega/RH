import Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCoefContSupp

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

/- English proof (translation)
Break down `h with _ | ⟨b, t⟩` into its components or cases. Both sides reduce to the same expression. It suffices to derive a contradiction. Establish `h1` using `(hh.1 b (by simp)).1`. Establish `h2` using `hh.2`.

Rewrite `h2` using `[Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons]`. Use linear arithmetic over natural numbers and integers.
-/
theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

/- English proof (translation)
Establish `hh0 : h = []` using `locPt_zero hh hR`. Substitute `hh0` using the available equality. Break down `P with ⟨k, r, T, T', u, u'⟩` into its components or cases. Simplify using `only at hR`. Substitute `hR` using the available equality.

Establish `e1 : p.ν' = ν'r`. Rewrite using `[← hν]`. Use function extensionality and compare the values at `i`. Simplify using `only [D.castV, liftVec]`. Rewrite using `[dif_pos (by simp; omega)]`.

Conclude with `congrArg ν'r (Fin.ext (by simp))`. Establish `e2 : p.m₀ = m₀r`. Rewrite using `[← hm]`. Use extensionality with `i j`. Simplify using `only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]`.

Rewrite using `[dif_pos (by simp; omega), dif_pos (by simp; omega)]`. Conclude with `congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))`. Establish `e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F`. Use function extensionality and compare the values at `γ`. Simplify using `only [D.castF]`.

Use `(Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_` and prove the remaining obligations. Conclude with `congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)`. Simplify using `only [List.nil_append]`. Rewrite using `[e3]`. Substitute `e1` using the available equality.

Substitute `e2` using the available equality. Both sides reduce to the same expression.
-/
theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dif_pos (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
