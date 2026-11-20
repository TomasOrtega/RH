import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ChartInv

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Unfold `comp1 ev`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨a, j⟩` from `p`. Use `fin_cases a`.

Both sides reduce to the same expression.
-/
theorem formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl

/- English proof (translation)
Use extensionality with `⟨a, i⟩ ⟨b, j⟩`. Take `rfl : b = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression.
-/
theorem linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  obtain rfl : b = 0 := Subsingleton.elim _ _
  rfl

/- English proof (translation)
Introduce `k _ d φ h0 hdet`. Establish `hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0` using `fun p => h0 p.2`. Establish `hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]`. Conclude with `hdet`.

Take `⟨v, hv, h1, h2⟩` from `(GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA`. Establish `hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v`. Use function extensionality and compare the values at `⟨a, j⟩`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression.

Use `⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[formalComp_apply_eq_mvPowerSeries_subst, hvv]`. Conclude with `h1 (0, i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[formalComp_apply_eq_mvPowerSeries_subst]`. Conclude with `h2 (0, i)`.
-/
theorem exists_isInvPair :
    ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
      IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi := by
  intro k _ d φ h0 hdet
  have hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0 :=
    fun p => h0 p.2
  have hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]
    exact hdet
  obtain ⟨v, hv, h1, h2⟩ := (GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA
  have hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v := by
    funext ⟨a, j⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst, hvv]
    exact h1 (0, i)
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst]
    exact h2 (0, i)

end GlobalTheory.ChartInv
