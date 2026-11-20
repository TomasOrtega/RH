import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBSelfAdj
import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Comm

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

/- English proof (translation)
Rewrite using `[Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]`.
-/
theorem pderiv_mul_free (v : σ) (g f : MvPolynomial σ ℚ_[p]) (hg : pderiv v g = 0) :
    pderiv v (g * f) = g * pderiv v f := by
  rw [Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_pair_free (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    pderiv v (∑ c, X (w c) * X (e c) : MvPolynomial σ ℚ_[p]) = 0 := by
  classical
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]
  simp

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Use `show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)`. Rewrite using `[pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]`.
-/
theorem commute_E_pderiv (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)
  rw [pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]

/- English proof (translation)
Unfold `Formalism.GM.tieF`. Use `Commute.sum_right _ _ _ fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp]`. Conclude with `(commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))`.
-/
theorem commute_E_F (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact (commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right
    (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Use `show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) = (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem commute_E_E (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieE (k := ℚ_[p]) w' e') := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) =
    (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)
  ring

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Unfold `Formalism.GM.tieF`. Use `Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]`. Establish `h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap)` using `(Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))`. Establish `h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap)` using `(Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))`.

Conclude with `h1.mul_left h2`.
-/
theorem commute_F_F (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieF (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))
  have h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))
  exact h1.mul_left h2

/- English proof (translation)
Establish `cEE` using `commute_E_E (p := p) w e w' e'`. Establish `cFF` using `commute_F_F (p := p) w e w' e'`. Establish `cEF` using `commute_E_F (p := p) w e w' e' h1 h2 h3 h4`. Establish `cFE` using `(commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm) (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm`. Establish `cP : Commute (Formalism.GM.tiePhi (k` using `ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by`.

Unfold `Formalism.GM.tiePhi`. Use `Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_` and prove the remaining obligations. Use `(Commute.smul_left ?_ _).smul_right _` and prove the remaining obligations. Rewrite using `[← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]`. Conclude with `((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))`.

Conclude with `LinearMap.congr_fun cP.eq x`.
-/
theorem commute_tiePhi (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') (o n z o' n' z' : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.tiePhi w e o n z (Formalism.GM.tiePhi w' e' o' n' z' x) = Formalism.GM.tiePhi w' e' o' n' z' (Formalism.GM.tiePhi w e o n z x) := by
  have cEE := commute_E_E (p := p) w e w' e'
  have cFF := commute_F_F (p := p) w e w' e'
  have cEF := commute_E_F (p := p) w e w' e' h1 h2 h3 h4
  have cFE := (commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm)
    (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm
  have cP : Commute (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by
    unfold Formalism.GM.tiePhi
    refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_
    refine (Commute.smul_left ?_ _).smul_right _
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact ((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))
  exact LinearMap.congr_fun cP.eq x

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
