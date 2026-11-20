import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def GramPres : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ (g : HA (AF F) σ J) (X : Fin a → Fin M → AF F ⊗[F] E),
    gramR (AF F) σ J (g • X) = gramR (AF F) σ J X

def PullLoc : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (g : HA (AF F) σ J) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    ∃ (Φinf' : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf' : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf' ∧ HasCompactSupport Φinf' ∧ IsPureFin b Φf' Φv' ∧
      IsProdInfFin (fun X => Φ (g • X)) Φinf' Φf' ∧
      (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
        ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
        ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
        ∫ X, Φinf' X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
        ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
        ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
        IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
        ∫ X, Φv' v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y)` using `(continuous_smul_tup σ J g).measurable`. Establish `hG'` using `hG F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hS : MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))}` using `(isClosed_eq (continuous_gramR (AF F) σ J) continuous_const).measurableSet.compl`. Rewrite using `[Measure.map_apply hm hS]`. Establish `e : (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))}`. Use extensionality with `X`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, hG' X]`.

Rewrite using `[e]`. Conclude with `hν.1`. Take `⟨⟨μinf, hμinf⟩, a1⟩` from `hν.2`. Use `⟨⟨μinf, hμinf⟩, fun μinf hμinf => ?_⟩` and prove the remaining obligations. Take `⟨⟨νinf, hνinf⟩, a2⟩` from `a1 μinf hμinf`.

Use `⟨⟨νinf, hνinf⟩, fun νinf hνinf => ?_⟩` and prove the remaining obligations. Take `⟨⟨μv, hμv⟩, a3⟩` from `a2 νinf hνinf`. Use `⟨⟨μv, hμv⟩, fun μv hμv => ?_⟩` and prove the remaining obligations. Take `⟨⟨νv, hνv⟩, a4⟩` from `a3 μv hμv`. Use `⟨⟨νv, hνv⟩, fun νv hνv => ?_⟩` and prove the remaining obligations.

Take `⟨⟨fibInf, hfi⟩, a5⟩` from `a4 νv hνv`. Use `⟨⟨fibInf, hfi⟩, fun fibInf hfi => ?_⟩` and prove the remaining obligations. Take `⟨⟨fibV, hfv⟩, a6⟩` from `a5 fibInf hfi`. Use `⟨⟨fibV, hfv⟩, fun fibV hfv => ?_⟩` and prove the remaining obligations. Introduce `d b Φ Φinf Φf Φv hcΦ hcs hpure hprod`.

Take `⟨Φinf', Φf', Φv', hc', hcs', hpure', hprod', hI, hV⟩` from `hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs hpure hprod`. Take `⟨hint, hmult, heq⟩` from `a6 fibV hfv d b (fun X => Φ (g • X)) Φinf' Φf' Φv' hc' hcs' hpure' hprod'`. Establish `hΦm : Measurable Φ` using `TopoMeas.measurable_adm Φ ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩`. Establish `eI` using `hI μinf hμinf νinf hνinf fibInf hfi`. Establish `eV : (fun v => ∫ X, Φv' v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) = fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))`.

Use function extensionality and compare the values at `fun v => hV v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v)`. Use `⟨(integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).2 hint, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← eV]`. Conclude with `hmult`. Rewrite using `[integral_map hm.aemeasurable hΦm.aestronglyMeasurable, ← eI, ← eV]`.

Conclude with `heq`.
-/
theorem omInv_of (hG : GramPres) (hP : PullLoc) : OmInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have hG' := hG F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  refine ⟨?_, ?_⟩
  · have hS : MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} :=
      (isClosed_eq (continuous_gramR (AF F) σ J) continuous_const).measurableSet.compl
    rw [Measure.map_apply hm hS]
    have e : (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) ⁻¹'
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} =
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hG' X]
    rw [e]
    exact hν.1
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  refine ⟨⟨μinf, hμinf⟩, fun μinf hμinf => ?_⟩
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  refine ⟨⟨νinf, hνinf⟩, fun νinf hνinf => ?_⟩
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  refine ⟨⟨μv, hμv⟩, fun μv hμv => ?_⟩
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  refine ⟨⟨νv, hνv⟩, fun νv hνv => ?_⟩
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  refine ⟨⟨fibInf, hfi⟩, fun fibInf hfi => ?_⟩
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  refine ⟨⟨fibV, hfv⟩, fun fibV hfv => ?_⟩
  intro d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨Φinf', Φf', Φv', hc', hcs', hpure', hprod', hI, hV⟩ :=
    hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨hint, hmult, heq⟩ := a6 fibV hfv d b (fun X => Φ (g • X)) Φinf' Φf' Φv' hc' hcs' hpure'
    hprod'
  have hΦm : Measurable Φ :=
    TopoMeas.measurable_adm Φ ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩
  have eI := hI μinf hμinf νinf hνinf fibInf hfi
  have eV : (fun v => ∫ X, Φv' v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
      fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    funext fun v => hV v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v)
  refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).2 hint, ?_, ?_⟩
  · rw [← eV]; exact hmult
  · rw [integral_map hm.aemeasurable hΦm.aestronglyMeasurable, ← eI, ← eV]
    exact heq

/- English proof (translation)
The claim follows from `nuInv_of (omUniq_of hD) (omInv_of hG hP)`.
-/
theorem nuInv_of_loc (hG : GramPres) (hP : PullLoc) (hD : DetAdm) : NuInv :=
  nuInv_of (omUniq_of hD) (omInv_of hG hP)

end PI.VolStabS
