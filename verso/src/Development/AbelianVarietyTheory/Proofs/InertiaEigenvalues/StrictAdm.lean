import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.StrictAdm

/- English proof (translation)
Introduce `D l _ K LL T₀ T₁ T₂ ι π hses hc`. Take `⟨hi, hs, -, hk, -⟩` from `hses`. Establish `hT` using `D.locT l`. Establish `hsq₀` using `(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi hc`. Establish `hsq₂` using `((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs hc).1`.

Establish `hdr` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ hc).1`. Establish `hrk : LinearMap.range ι.f = LinearMap.ker π.f`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_range, LinearMap.mem_ker, hk x]`. Establish `he` using `GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv hi hs hrk hdr`.

Conclude with `⟨hsq₀, hsq₂, fun τ a => (he.2.2 τ a).2.1⟩`.
-/
theorem strict_adm : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm11 D := by
  intro D l _ K LL T₀ T₁ T₂ ι π hses hc
  obtain ⟨hi, hs, -, hk, -⟩ := hses
  have hT := D.locT l
  have hsq₀ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi hc
  have hsq₂ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs hc).1
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ hc).1
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, hk x]
  have he := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ
    ι.f π.f ι.equiv π.equiv hi hs hrk hdr
  exact ⟨hsq₀, hsq₂, fun τ a => (he.2.2 τ a).2.1⟩

end GlobalTheory.Per.StrictAdm
