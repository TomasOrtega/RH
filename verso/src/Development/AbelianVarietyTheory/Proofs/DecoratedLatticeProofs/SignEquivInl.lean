import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def signEquiv {n : ℕ} (ε : Fin n → Bool) {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : Fin n ≃ Fin p ⊕ Fin q :=
  (Equiv.sumCompl fun a => ε a = true).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; exact hp))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simpa using hq)))

/- English proof (translation)
Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. A detailed English derivation is pending.
-/
theorem signEquiv_inl {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin p) : ε ((signEquiv ε hp hq).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  generalize (Fintype.equivFinOfCardEq (α := {a // ε a = true}) _).symm i = x
  exact x.2

/- English proof (translation)
Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. Simplify to obtain the desired conclusion from the available facts.
-/
theorem signEquiv_inr {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin q) : ε ((signEquiv ε hp hq).symm (Sum.inr i)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  generalize (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) _).symm i = x
  simpa using x.2

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem card_true (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = true).card = (V.sig (tauE D τ)).1 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).1

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem card_false (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).2

def sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Mem.Th.CptF V := fun τ =>
  (M.fr τ).submatrix (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ)).symm id

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Simplify the hypotheses and the goal together.
-/
theorem Jpq_submatrix {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    (Formalism.UG.Jpq p q).submatrix (signEquiv ε hp hq) (signEquiv ε hp hq) = Formalism.REAL.Jm ε := by
  ext a b
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rcases h1 : signEquiv ε hp hq a with i | i
    · have := signEquiv_inl hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
    · have := signEquiv_inr hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
  · have hne : signEquiv ε hp hq a ≠ signEquiv ε hp hq b := (signEquiv ε hp hq).injective.ne hab
    rw [if_neg hab]
    rcases h1 : signEquiv ε hp hq a with i | i <;> rcases h2 : signEquiv ε hp hq b with j | j <;> rw [h1, h2] at hne <;>
      simp_all [Formalism.UG.Jpq, Matrix.one_apply]

end GlobalTheory.ChainOnto.RealData

end
