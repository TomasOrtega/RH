import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord.FrobMove

/- English proof (translation)
Establish `hd : (M.map f).det = f M.det` using `(RingHom.map_det f M).symm`. Establish `ha : (M.map f).adjugate = M.adjugate.map f` using `(RingHom.map_adjugate f M).symm`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, hd, ha]`. Use extensionality with `i j`. Simplify using `[Ring.inverse_eq_inv', map_inv₀]`.
-/
theorem inv_map_field {E K : Type*} [Field E] [Field K] (f : E →+* K) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) : (M.map f)⁻¹ = M⁻¹.map f := by
  have hd : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  have ha : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm
  rw [Matrix.inv_def, Matrix.inv_def, hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

/- English proof (translation)
The claim follows from `D.host.φ₀.injective (by rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])`.
-/
theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

/- English proof (translation)
Introduce `D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b`. Use `choose ρ hρ using exists_ringHom_rhoK D lam σ hσ hcl`. Establish `hfun : ∀ z, rhoK D lam z = ⇑(ρ z)` using `fun z => funext fun y => (hρ z y).1`. Establish `hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y)` using `fun z y => by`. Rewrite using `[← (hρ z y).1, ← (hρ _ _).1]`.

Conclude with `sigma_rhoK D lam σ hσ hcl z y`. Establish `hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E), (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1))` using `fun z Q => by`. Use extensionality with `i j`. Simplify using `[hs]`. Establish `hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j, σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j` using `fun z Q i j => by`.

Rewrite using `[← hsm, inv_map_field σ]`. Both sides reduce to the same expression. Establish `K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E), (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z, ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose * ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z …`. Introduce `n Q hQ z`. Establish `e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose * ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1))`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[conj_conj]`. Rewrite using `[e, hQ z]`.

Simplify using the standard rewrite rules. Establish `K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E), (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z, (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ = ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))). …` using `fun Q hQ z => Matrix.inv_eq_left_inv (K Q hQ z)`. Establish `K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E), (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z, ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹). …` using `fun Q hQ z => by`. Rewrite using `[Matrix.transpose_nonsing_inv]`. Conclude with `(Matrix.inv_eq_right_inv (K Q hQ z)).symm`.

Establish `hPc` using `hP.2.1 hcl`. Establish `hP'c` using `hP'.2.1 hcl`. Use `⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩` and prove the remaining obligations. Simplify using `only [gK, hK, hfun, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_` and prove the remaining obligations.

Rewrite using `[hs, hs, conj_conj, hinv, K1 P hPc z]`. Establish `e2` using `congrFun (congrFun (K2 P' hP'c z) b₁) b₀`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [gK, hK, hfun, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_` and prove the remaining obligations. Rewrite using `[hs, hs, hinv, K1 P' hP'c w]`. Establish `e2` using `congrFun (congrFun (K2 P hPc w) a₁) a`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢`.

Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frob_moves_coords : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b
  choose ρ hρ using exists_ringHom_rhoK D lam σ hσ hcl
  have hfun : ∀ z, rhoK D lam z = ⇑(ρ z) := fun z => funext fun y => (hρ z y).1
  have hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y) := fun z y => by
    rw [← (hρ z y).1, ← (hρ _ _).1]; exact sigma_rhoK D lam σ hσ hcl z y
  have hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E),
      (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1)) := fun z Q => by
    ext i j; simp [hs]
  have hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j,
      σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j := fun z Q i j => by
    rw [← hsm, inv_map_field σ]; rfl
  have K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = 1 := by
    intro n Q hQ z
    have e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map
          (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1)) := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp [conj_conj]
    rw [e, hQ z]
    simp
  have K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ =
        ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose := fun Q hQ z =>
    Matrix.inv_eq_left_inv (K Q hQ z)
  have K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹).transpose := fun Q hQ z => by
    rw [Matrix.transpose_nonsing_inv]; exact (Matrix.inv_eq_right_inv (K Q hQ z)).symm
  have hPc := hP.2.1 hcl
  have hP'c := hP'.2.1 hcl
  refine ⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩
  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, conj_conj, hinv, K1 P hPc z]
    have e2 := congrFun (congrFun (K2 P' hP'c z) b₁) b₀
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring
  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, hinv, K1 P' hP'c w]
    have e2 := congrFun (congrFun (K2 P hPc w) a₁) a
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring

end GlobalTheory.KerStd.HypCoord.FrobMove
