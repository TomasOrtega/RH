import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ShinGaloisRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ChenevierHarris
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiNearbyCycles
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiPureAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveLSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.GalCut

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc`. Take `⟨p, hp⟩` from `hiso`. Establish `hcw : ∀ {A : ValuationSubring Ω} (h : IsPlaceOver A w) (g : Weil h), p * r g = r' g * p` using `fun h g => by rw [hp]; group`. Establish `hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F` using `E) A)), r'.comp (Dec (F := E) A).subtype g = p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g`. Consider the cases of `c with`.

Consider the case `ss`. Introduce `hl A h rc hrc σ hσ g`. Rewrite using `[← wdOf_eq_of_conj hl p (hcw h)]`. Conclude with `hc hl A h rc hrc σ hσ g`. Consider the case `pure`.

Introduce `hl A h wt hwt`. Rewrite using `[← wdOf_eq_of_conj hl p (hcw h)]`. Conclude with `hc hl A h wt hwt`. Consider the case `dR`. Introduce `P AI hT A hA O _ _ _ Bw hj`.

Take `⟨h1, h2⟩` from `hc P AI hT A hA O Bw hj`. Take `⟨k1, -, -, k4⟩` from `GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)`. Conclude with `⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩`. Consider the case `crys`. Introduce `P AI hT A hA O _ _ _ Bw hj σ hσ hS`.

Take `⟨-, k2, -, -⟩` from `GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)`. Conclude with `k2 (hc P AI hT A hA O Bw hj σ hσ hS)`. Consider the case `iwa`. Introduce `P AI hT A h O _ _ _ Bw hj σ hσ hI`. Take `⟨h3, h4⟩` from `hc P AI hT A h O Bw hj σ hσ hI`.

Conclude with `⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc => (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩`.
-/
theorem clauseAt_of_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → UpperTheory.V.Af.RepIso r r' → ∀ c w, ClauseAt c π ι r w → ClauseAt c π ι r' w := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc
  obtain ⟨p, hp⟩ := hiso
  have hcw : ∀ {A : ValuationSubring Ω} (h : IsPlaceOver A w) (g : Weil h), p * r g = r' g * p :=
    fun h g => by rw [hp]; group
  have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
      p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
  cases c with
  | ss =>
    intro hl A h rc hrc σ hσ g
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h rc hrc σ hσ g
  | pure =>
    intro hl A h wt hwt
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h wt hwt
  | dR =>
    intro P AI hT A hA O _ _ _ Bw hj
    obtain ⟨h1, h2⟩ := hc P AI hT A hA O Bw hj
    obtain ⟨k1, -, -, k4⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact ⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩
  | crys =>
    intro P AI hT A hA O _ _ _ Bw hj σ hσ hS
    obtain ⟨-, k2, -, -⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact k2 (hc P AI hT A hA O Bw hj σ hσ hS)
  | iwa =>
    intro P AI hT A h O _ _ _ Bw hj σ hσ hI
    obtain ⟨h3, h4⟩ := hc P AI hT A h O Bw hj σ hσ hI
    exact ⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc =>
      (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩

end GlobalTheory.GalCut
