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
Establish `hP` using `Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ`. Establish `hlh` using `Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hl`. Establish `hspec` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hl).1`. Establish `hspech` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlh).1`. Apply the tactic sequence `have entry : ∀ {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (x y : Fin p), U.hMat σ d x y = if σ x = y then d y else 0 := by`.

Introduce `p σ d x y`. Simplify using `only [U.hMat, Matrix.mul_diagonal, U.wP, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[entry]`. Establish `hpa : ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) = if a' < D.ptSize h then D.ptPartner h a' else D.ptSize h + (s - 1 - (a' - D.ptSize h))`.

Rewrite using `[hspec ⟨a', ha'⟩]`. Conclude with `Formalism.FourierDecayAlt.P.Dx2.SL.partner_append s τ h a' (by omega)`. Establish `hdq : D.ptDiag (h ++ [(s, τ)]) ⟨q, hq⟩ = if q < D.ptSize h then D.ptScal h q else τ`. Simplify using `only [D.ptDiag]`. Conclude with `Formalism.FourierDecayAlt.P.Dx2.SL.scal_append s τ h q (by omega)`.

Establish `heq : (D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ = ⟨q, hq⟩) ↔ ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) = q`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[e]`. Introduce `e`.

Conclude with `Fin.ext e`. Unfold `C3.Zb`. Distinguish the cases in `h1 : a' < D.ptSize h`. Rewrite using `[dif_pos h1]`. Establish `hpart : D.ptPartner h a' < D.ptSize h`.

Rewrite using `[← hspech ⟨a', h1⟩]`. Conclude with `(D.ptPerm h ⟨a', h1⟩).isLt`. Distinguish the cases in `h2 : q < D.ptSize h`. Rewrite using `[dif_pos h2, entry]`. Establish `heqh : (D.ptPerm h ⟨a', h1⟩ = ⟨q, h2⟩) ↔ D.ptPartner h a' = q`.

Rewrite using `[← hspech ⟨a', h1⟩]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[e]`. Introduce `e`.

Conclude with `Fin.ext e`. Distinguish the cases in `h3 : D.ptPartner h a' = q`. Rewrite using `[if_pos (heq.2 (by rw [hpa, if_pos h1]; exact h3)), if_pos (heqh.2 h3), hdq, if_pos h2]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun e => h3 (by rw [heq] at e; rw [hpa, if_pos h1] at e; exact e)), if_neg (fun e => h3 (heqh.1 e))]`.

Rewrite using `[dif_neg h2, if_neg]`. Introduce `e`. Rewrite `e` using `[heq, hpa, if_pos h1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h1]`.

Distinguish the cases in `h3 : D.ptSize h ≤ q ∧ a' < D.ptSize h + s ∧ q < D.ptSize h + s ∧ (a' - D.ptSize h) + (q - D.ptSize h) + 1 = s`. Rewrite using `[if_pos h3, if_pos (heq.2 (by rw [hpa, if_neg h1]; omega)), hdq, if_neg (by omega)]`. Rewrite using `[if_neg h3, if_neg]`. Introduce `e`. Rewrite `e` using `[heq, hpa, if_neg h1]`.

Apply `h3` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
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
Simplify using `only [Sset, Set.mem_setOf_eq]`. Use `⟨1, ?_, 1, ?_, (Matrix.mul_one 1).symm⟩` and prove the remaining obligations. Simplify using `[Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.UH]`. Simplify using `[Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Matrix.one_apply]`.
-/
theorem one_mem_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_, (Matrix.mul_one 1).symm⟩
  · simp [Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.UH]
  · simp [Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Matrix.one_apply]

/- English proof (translation)
Establish `hD : Dmin k r z z' (s * g) ⟨j, by omega⟩ = Dmin k r z z' g ⟨j, by omega⟩`. Use `Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' s hs 1 (one_mem_Sset k r z') g ⟨j, by omega⟩` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Then use the resulting hypothesis. Establish `hA` using `AAInvW.left_aa E k r z (j - e) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) K s g hs hg`. Unfold `D.vLet`.

Rewrite using `[hD, hA.1.symm, hA.2.symm]`.
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
Take `⟨U, f', hU, hsxU, hf', he⟩` from `h`. Establish `hc : Continuous (fun y : B.Mat k r => s * y)` using `continuous_const.mul continuous_id`. Use `⟨(fun y => s * y) ⁻¹' U, fun y => f' (s * y), hU.preimage hc, hsxU, ?_, fun y hy hyG => ?_⟩` and prove the remaining obligations. Set `L : B.Mat k r →ₗ[ℝ] B.Mat k r` to `{ toFun := fun y => s * y, map_add' := fun a b => Matrix.mul_add s a b, map_smul' := fun c y => Matrix.mul_smul s c y }`. Establish `hl : ContDiff ℝ (⊤ : ℕ∞) (fun y : B.Mat k r => s * y)` using `(LinearMap.toContinuousLinearMap L).contDiff`.

Conclude with `hf'.comp hl.contDiffOn (fun y hy => hy)`. Conclude with `he _ hy (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hyG)`.
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
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hf', he⟩` from `h g₀ hg₀`. Conclude with `⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgl => he g hg hgl.1⟩`.
-/
theorem smoothLev_of_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {D : Set (Q.Mx k r)} (h : ∀ x ∈ Q.Glev k r 0 ∩ D, CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K x) : Q.SmoothLev k r 0 D K := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgl => he g hg hgl.1⟩

end Formalism.FourierDecayAlt.P.PBG
