import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTupleGramDetNeZero

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibre

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2`. Take `⟨X0, hdet, hT⟩` from `GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)`. Establish `hI : PI.VolStabS.FibInfEx` using `PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds PI.VolStabS.densInf_holds`. Establish `hV : PI.VolStabS.FibVEx` using `PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds PI.VolStabS.densV_holds`. Take `⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩` from `PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ`.

Establish `hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ` using `⟨_, hμv v⟩`. Establish `hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν` using `⟨_, hνv v⟩`. Establish `hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a)`. Unfold `Formalism.L2.SG.LocVol.dX`. Rewrite using `[dif_pos hX]`.

Conclude with `hX.choose_spec`. Establish `hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a)`. Unfold `Formalism.L2.SG.LocVol.dT`. Rewrite using `[dif_pos hH]`. Conclude with `hH.choose_spec`.

Establish `hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib` using `hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT`. Use `⟨hdX.1, hdT.1, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.SG.LocVol.omFam`. Rewrite using `[dif_pos hO]`. Conclude with `hO.choose_spec`.
-/
theorem dX_dT_omFam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2
  obtain ⟨X0, hdet, hT⟩ := GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)
  have hI : PI.VolStabS.FibInfEx :=
    PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densInf_holds
  have hV : PI.VolStabS.FibVEx :=
    PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densV_holds
  obtain ⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩ :=
    PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet
      ψ hψ
  have hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨_, hμv v⟩
  have hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨_, hνv v⟩
  have hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dX
    rw [dif_pos hX]
    exact hX.choose_spec
  have hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dT
    rw [dif_pos hH]
    exact hH.choose_spec
  have hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib :=
    hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT
  refine ⟨hdX.1, hdT.1, ?_⟩
  unfold Formalism.L2.SG.LocVol.omFam
  rw [dif_pos hO]
  exact hO.choose_spec

end GlobalTheory.LocalFibre
