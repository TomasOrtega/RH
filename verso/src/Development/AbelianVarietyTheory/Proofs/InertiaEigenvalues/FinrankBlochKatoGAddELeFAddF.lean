import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAnnihilatorAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompareStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatumStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

/- English proof (translation)
Introduce `l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual`. Use `letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])`. Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])`. Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

Establish `hO` using `GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)`. Establish `hTD` using `CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate`. Establish `hEC` using `CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler`. Set `A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l]` to `{ V := V, ρ := ρ, cont := hc }`. Set `A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l]` to `{ V := V', ρ := ρ', cont := hc' }`.

Establish `hdual' : IsDual1 (P.PD K) ρ' ρ m.flip`. Take `⟨h1, h2, h3, h4⟩` from `hdual`. Use `⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩` and prove the remaining obligations. Simplify using `only [LinearMap.flip_apply]`. Conclude with `h1 g x y`.

Take `⟨hfin, -⟩` from `GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual`. Take `⟨hfin', -⟩` from `GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'`. Use `haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin`. Use `haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'`. Take `⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l], (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ'` from `GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual`.

Establish `hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔ ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b))` using `(GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1`. Establish `horth` using `GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual`. Establish `hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ` using `fun _ h => h.1`. Establish `he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ'` using `fun _ h => h.1`. Establish `hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ` using `fun _ h => h.1`.

Establish `hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ'` using `fun _ h => h.1`. Establish `hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ'` using `GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'`. Establish `hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ'`. Introduce `c hcB`. Use `⟨hf' (hBf hcB), ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `hcB`. Use `⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩` and prove the remaining obligations. Simplify using `[φVB]`. Simplify using `[cob, actVB, sub_tmul]`. Establish `key` using `GlobalTheory.HyodoDef.PairLin.finrank_add_le β ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD …`.

Rewrite using `[Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]`. Prove the components needed by the constructor for the conclusion. Introduce `h b hb`. Conclude with `(hβ a b).2 (h b.1 hb)`. Introduce `h b hb`.

Conclude with `(hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))`. Rewrite `key` using `[(Submodule.comapSubtypeEquivOfLe hg).finrank_eq, (Submodule.comapSubtypeEquivOfLe he).finrank_eq, (Submodule.comapSubtypeEquivOfLe hf).finrank_eq, (Submodule.comapSubtypeEquivOfLe hf').finrank_eq]`. Then use the resulting hypothesis.
-/
theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
