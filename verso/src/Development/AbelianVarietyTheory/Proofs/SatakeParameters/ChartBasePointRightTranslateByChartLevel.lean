import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalConditionInvariantRightLevelTranslateStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartLevelBaseFrameCongrOneAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslateStatement

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Use `Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_` and prove the remaining obligations. Establish `h1` using `Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz`. Establish `h2 : bc (prV (E` using `E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)`. Establish `h3` using `(h2.2 _).1 h1`. Establish `e : (fun i => prV (E` using `E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) = ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ fun i => prV (E := E) v (z i) := by`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i`. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem levU_mulVec_mem_hatL (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

/- English proof (translation)
Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `levU_mulVec_mem_hatL S κ.1 κ.2 _ hz` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Introduce `hz`. Conclude with `levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz`.
-/
theorem hatStab_of_levU (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := levU_mulVec_mem_hatL S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end Hat

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp`. Take `⟨p', hN, hf, hfr⟩` from `GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) (GlobalTheory.T.chartLevel_baseFrame_congr_ …`. Use `⟨p', ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hN, hp.lat]`. Unfold `latCo`.

Rewrite using `[hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]`. Introduce `P`. Establish `e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) = ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) * ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))`. Rewrite using `[hx]`. Simplify using `only [mul_assoc, mul_inv_cancel_left]`.

Rewrite using `[e]`. Conclude with `hfr P`. Introduce `P v h hv`. Establish `e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1`. Rewrite using `[hx, mul_assoc]`.

Establish `h1` using `GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)`. Rewrite using `[e]`. Introduce `w hw z hz`. Establish `h2` using `h1 w (by rw [← hN]; exact hw) z hz`. Conclude with `(congrFun (congrFun hf P) w).trans h2`.
-/
theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp
  obtain ⟨p', hN, hf, hfr⟩ := GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p
    (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))
    (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))
    (GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime A dtU a hP H i hi β x p κ hp) hp.frame
  refine ⟨p', ⟨?_, ?_, ?_⟩⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]
  · intro P
    have e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) =
        ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact hfr P
  · intro P v h hv
    have e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by
      rw [hx, mul_assoc]
    have h1 := GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)
    rw [e]
    intro w hw z hz
    have h2 := h1 w (by rw [← hN]; exact hw) z hz
    exact (congrFun (congrFun hf P) w).trans h2

end GlobalTheory.TwV

end
