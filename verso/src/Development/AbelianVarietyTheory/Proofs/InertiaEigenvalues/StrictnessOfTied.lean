import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FilteredIsoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

namespace GlobalTheory.FontaineExtensionCriteria

open GlobalTheory.Per.FontaineBound in

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO A`. Establish `: FiniteDimensional ℚ_[l] LL` using `hO.2.1`. Establish `hd` using `ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ`. Use `⟨?_, hd, fun hc => ?_⟩` and prove the remaining obligations. Use `isDomain_cris (P.PD K) (isField_of_tied T)` as an intermediate fact.

Use `(P.PD K).finK₀` as an intermediate fact. Use `finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ` and prove the remaining obligations. Establish `h1` using `h ⟨g, hg⟩`. Rewrite `h1` using `[P.PD_actB, P.PD_actB]`. Rewrite using `[mul_comm, h1, mul_comm]`.

Use `(GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1` and prove the remaining obligations. Simplify `hb` using `only [P.PD_ι]`.
-/
theorem fontCore_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) : LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  have : FiniteDimensional ℚ_[l] LL := hO.2.1
  have hd := ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ
  refine ⟨?_, hd, fun hc => ?_⟩
  · have := isDomain_cris (P.PD K) (isField_of_tied T)
    have := (P.PD K).finK₀
    refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  · refine (GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ
      (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1
    simpa only [P.PD_ι] using hb

/- English proof (translation)
The claim follows from `(GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1`.
-/
theorem strictness_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  (GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1

/- English proof (translation)
Introduce `P _ ⟨T⟩` and use `GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)`.
-/
theorem extCrys_of_tied : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P :=
  fun P _ ⟨T⟩ => GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)

end GlobalTheory.FontaineExtensionCriteria
