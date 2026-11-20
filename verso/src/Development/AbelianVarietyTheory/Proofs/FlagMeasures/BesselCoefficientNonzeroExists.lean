import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinNeZeroOfCwCont
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

/- English proof (translation)
Introduce `H k r L l l' κ τ hκ hτ hl hl' hxe hye`. Establish `hK : PI.KFinSmooth` using `H.1.2.2.1`. Establish `hDS : (rep L).IsDS L.ε L.lam` using `⟨L.hlam, L.hσ⟩`. Take `⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩` from `GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS`. Establish `hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v)` using `hmul0`.

Establish `hone : ∀ v : L.Hs, L.σ 1 v = v` using `hone0`. Establish `hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ` using `hinn0`. Establish `hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ` using `GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ`. Establish `hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r` using `Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ`. Establish `hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r` using `Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ`.

Establish `hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v`. Introduce `v`. Rewrite using `[← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]`. Establish `side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V), SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) → ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0`. Introduce `V _ _ _ m hm ⟨x, hxT, hx⟩`.

Use `haveI := FiniteDimensional.complete ℂ V`. Use `GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `v hv w hw`. Conclude with `(congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))`. Introduce `a v hv`.

Conclude with `(congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))`. Conclude with `GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2`. Use `⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩` and prove the remaining obligations. Conclude with `fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)`. Take `⟨x₀, hx₀, hx₀'⟩` from `side l hl hxe`.

Take `⟨y₀, hy₀, hy₀'⟩` from `side l' hl' hye`. Use `set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ`. Use `set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'`. Set `P : L.Hs →L[ℂ] L.Wp` to `(innerSL ℂ x₀).smulRight ξ`. Set `Q : L.Wq →L[ℂ] L.Hs` to `(innerSL ℂ ξ').smulRight y₀`.

Set `X : L.Wq →L[ℂ] L.Wp` to `(innerSL ℂ ξ').smulRight ξ`. Establish `hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ` using `fun v => rfl`. Establish `hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀` using `fun w => rfl`. Establish `hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ` using `fun w => rfl`. Use `⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w`. Take `⟨S, hS, hyS, hSK⟩` from `hy₀`. Use `⟨S, hS, ?_, hSK⟩` and prove the remaining obligations. Rewrite using `[hQ]`. Conclude with `S.smul_mem _ hyS`.

Introduce `v`. Establish `hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `u`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]`.

Rewrite using `[hadj]`. Take `⟨S, hS, hxS, hSK⟩` from `hx₀`. Conclude with `⟨S, hS, S.smul_mem _ hxS, hSK⟩`. Use `⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀, fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Establish `key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) = (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)))`. Use extensionality with `v`. Use `show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _`. Rewrite using `[hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]`. Both sides reduce to the same expression.

Establish `key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ = ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ`. Introduce `u`. Rewrite using `[← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]`. Use extensionality with `w`. Simplify using `only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX, map_smul, key2, inner_smul_right, smul_smul, mul_comm]`.

Conclude with `congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)`. Simplify using `only [Fin.sum_univ_one]`. Both sides reduce to the same expression. Rewrite using `[hX, inner_smul_right]`. Conclude with `mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')`.
-/
theorem exists_kFinCoef_torus_ne : BranchingSupport.Hyps → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.AmpTK
