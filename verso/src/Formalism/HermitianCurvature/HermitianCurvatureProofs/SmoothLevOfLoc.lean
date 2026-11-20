import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.LyQminorLeft
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem hmat_zb (h : C.LPt) (s : ℕ) (τ : ℂ) (hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])))
    (a' q : ℕ) (ha' : a' < D.ptSize (h ++ [(s, τ)])) (hq : q < D.ptSize (h ++ [(s, τ)])) :
    U.hMat (D.ptPerm (h ++ [(s, τ)])) (D.ptDiag (h ++ [(s, τ)])) ⟨a', ha'⟩ ⟨q, hq⟩ =
      C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a' q := by
  have hP := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hlh := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hl
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hl).1
  have hspech := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlh).1
  have entry : ∀ {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (x y : Fin p),
      U.hMat σ d x y = if σ x = y then d y else 0 := by
    intro p σ d x y
    simp only [U.hMat, Matrix.mul_diagonal, U.wP, Matrix.of_apply]
    split_ifs <;> simp
  rw [entry]
  have hpa : ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) =
      if a' < D.ptSize h then D.ptPartner h a' else D.ptSize h + (s - 1 - (a' - D.ptSize h)) := by
    rw [hspec ⟨a', ha'⟩]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.partner_append s τ h a' (by omega)
  have hdq : D.ptDiag (h ++ [(s, τ)]) ⟨q, hq⟩ = if q < D.ptSize h then D.ptScal h q else τ := by
    simp only [D.ptDiag]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.scal_append s τ h q (by omega)
  have heq : (D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ = ⟨q, hq⟩) ↔
      ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) = q := by
    constructor
    · intro e; rw [e]
    · intro e; exact Fin.ext e
  unfold C3.Zb
  by_cases h1 : a' < D.ptSize h
  · rw [dif_pos h1]
    have hpart : D.ptPartner h a' < D.ptSize h := by
      rw [← hspech ⟨a', h1⟩]; exact (D.ptPerm h ⟨a', h1⟩).isLt
    by_cases h2 : q < D.ptSize h
    · rw [dif_pos h2, entry]
      have heqh : (D.ptPerm h ⟨a', h1⟩ = ⟨q, h2⟩) ↔ D.ptPartner h a' = q := by
        rw [← hspech ⟨a', h1⟩]
        constructor
        · intro e; rw [e]
        · intro e; exact Fin.ext e
      by_cases h3 : D.ptPartner h a' = q
      · rw [if_pos (heq.2 (by rw [hpa, if_pos h1]; exact h3)), if_pos (heqh.2 h3), hdq, if_pos h2]
        rfl
      · rw [if_neg (fun e => h3 (by rw [heq] at e; rw [hpa, if_pos h1] at e; exact e)),
          if_neg (fun e => h3 (heqh.1 e))]
    · rw [dif_neg h2, if_neg]
      intro e
      rw [heq, hpa, if_pos h1] at e
      omega
  · rw [dif_neg h1]
    by_cases h3 : D.ptSize h ≤ q ∧ a' < D.ptSize h + s ∧ q < D.ptSize h + s ∧
        (a' - D.ptSize h) + (q - D.ptSize h) + 1 = s
    · rw [if_pos h3, if_pos (heq.2 (by rw [hpa, if_neg h1]; omega)), hdq, if_neg (by omega)]
    · rw [if_neg h3, if_neg]
      intro e
      rw [heq, hpa, if_neg h1] at e
      apply h3
      omega

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem one_mem_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_, (Matrix.mul_one 1).symm⟩
  · simp [Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.UH]
  · simp [Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Matrix.one_apply]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities.
-/
theorem vLet_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) (K : B.Mat k r → E)
    (s g : B.Mat k r) (hs : s ∈ Sset k r z) (hg : g ∈ B.GV k r) :
    D.vLet k r z z' j hj l e K (s * g) = D.vLet k r z z' j hj l e (fun x => K (s * x)) g := by
  have hD : Dmin k r z z' (s * g) ⟨j, by omega⟩ = Dmin k r z z' g ⟨j, by omega⟩ := by
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' s hs 1 (one_mem_Sset k r z') g ⟨j, by omega⟩
    rwa [Matrix.mul_one] at this
  have hA := AAInvW.left_aa E k r z (j - e) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)
    ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) K s g hs hg
  unfold D.vLet
  rw [hD, hA.1.symm, hA.2.symm]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem loc_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {s x : B.Mat k r} (hs : s ∈ B.GV k r) (h : CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K (s * x)) :
    CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (fun y => K (s * y)) x := by
  obtain ⟨U, f', hU, hsxU, hf', he⟩ := h
  have hc : Continuous (fun y : B.Mat k r => s * y) := continuous_const.mul continuous_id
  refine ⟨(fun y => s * y) ⁻¹' U, fun y => f' (s * y), hU.preimage hc, hsxU, ?_, fun y hy hyG => ?_⟩
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun y => s * y, map_add' := fun a b => Matrix.mul_add s a b,
        map_smul' := fun c y => Matrix.mul_smul s c y }
    have hl : ContDiff ℝ (⊤ : ℕ∞) (fun y : B.Mat k r => s * y) := (LinearMap.toContinuousLinearMap L).contDiff
    exact hf'.comp hl.contDiffOn (fun y hy => hy)
  · exact he _ hy (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hyG)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem smoothLev_of_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {D : Set (Q.Mx k r)} (h : ∀ x ∈ Q.Glev k r 0 ∩ D, CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K x) : Q.SmoothLev k r 0 D K := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgl => he g hg hgl.1⟩

end Formalism.FourierDecayAlt.P.PBG
