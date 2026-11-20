import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanDOfFixed

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedRestrict

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Introduce `x y hx h`. Use `GlobalTheory.T.ratio_invariant_in_K0 l P AI T K y x hx fun g hg => ?_` and prove the remaining obligations. Establish `h1` using `h ⟨g, hg⟩`. Establish `e : ∀ z, (P.PD K).actB ⟨g, hg⟩ z = P.actQ g z` using `fun z => P.PD_actB K ⟨g, hg⟩ z`. Rewrite `h1` using `[e, e]`.

Rewrite using `[mul_comm, h1, mul_comm]`.
-/
theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.T.ratio_invariant_in_K0 l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  have e : ∀ z, (P.PD K).actB ⟨g, hg⟩ z = P.actQ g z := fun z => P.PD_actB K ⟨g, hg⟩ z
  rw [e, e] at h1
  rw [mul_comm, h1, mul_comm]

variable {K K' LL : FinExt l} (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

/- English proof (translation)
Use `le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : actVB (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) = actVB (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g`. Unfold `actVB`. Use `congr 1`. Conclude with `LinearMap.ext fun z => (P.PD_actB K _ z).trans (P.PD_actB K' g z).symm`.

Rewrite using `[e]`.
-/
theorem dcris_le : Dcris (P.PD K) ρ ≤ Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  refine le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)
  have e : actVB (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) =
      actVB (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g := by
    unfold actVB
    congr 1
    exact LinearMap.ext fun z => (P.PD_actB K _ z).trans (P.PD_actB K' g z).symm
  rw [e]

/- English proof (translation)
Use `le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : actVdR (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) = actVdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g`. Unfold `actVdR`. Use `congr 1`. Conclude with `LinearMap.ext fun z => (P.PD_actdR K _ z).trans (P.PD_actdR K' g z).symm`.

Rewrite using `[e]`.
-/
theorem ddR_le : DdR (P.PD K) ρ ≤ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  refine le_iInf fun g => (iInf_le _ (Subgroup.inclusion (GK_le h) g)).trans (le_of_eq ?_)
  have e : actVdR (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) =
      actVdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g := by
    unfold actVdR
    congr 1
    exact LinearMap.ext fun z => (P.PD_actdR K _ z).trans (P.PD_actdR K' g z).symm
  rw [e]

variable [FiniteDimensional ↥LL.1 V]

/- English proof (translation)
Use `LL.2` as an intermediate fact. Establish `: IsDomain P.R.B` using `isDomain_of_tied T K`. Establish `: FiniteDimensional ℚ_[l] V` using `Module.Finite.trans ↥LL.1 V`. Take `⟨h1, -⟩` from `finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ`. Take `⟨h2, h3⟩` from `finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))`.

Rewrite `hc`, the goal using `[isCrys_iff_finrank]`. Use `le_antisymm h3 ?_` and prove the remaining obligations. Set `e` to `Module.finBasisOfFinrankEq ↥(K0 K) _ hc`. Establish `hB` using `indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent`. Set `d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))` to `fun i => ⟨e i, dcris_le h ρ (e i).2⟩`.

Establish `hd : LinearIndependent ↥(K0 K') d` using `LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype (hB.restrict_scalars' ↥(K0 K'))`. Simplify using `using hd.fintype_card_le_finrank`.
-/
theorem isCrys_restrict (T : LocTied l P AI) (hc : IsCrys (P.PD K) ρ) :
    IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨h1, -⟩ := finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ
  obtain ⟨h2, h3⟩ := finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))
  rw [isCrys_iff_finrank] at hc ⊢
  refine le_antisymm h3 ?_
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hc
  have hB := indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent
  let d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
    fun i => ⟨e i, dcris_le h ρ (e i).2⟩
  have hd : LinearIndependent ↥(K0 K') d :=
    LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype
      (hB.restrict_scalars' ↥(K0 K'))
  simpa using hd.fintype_card_le_finrank

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hd`. Establish `hs` using `(GlobalTheory.DRFil.filSpans T K LL ρ hd).spans _`. Use `GlobalTheory.DRFil.isDR_of_spans T K' LL _ fun y => ?_` and prove the remaining obligations. Take `⟨m, b, d, hm, e⟩` from `hs y`.

Conclude with `⟨m, b, d, fun i => ddR_le h ρ (hm i), e⟩`. Introduce `hd`. Conclude with `GlobalTheory.DRFil.isDR_of_spans T K LL ρ (GlobalTheory.DRFil.spans_descent l P K K' LL h V ρ ((GlobalTheory.DRFil.filSpans T K' LL _ hd).spans _))`.
-/
theorem isDR_restrict_iff (T : LocTied l P AI) :
    IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
  constructor
  · intro hd
    have hs := (GlobalTheory.DRFil.filSpans T K LL ρ hd).spans _
    refine GlobalTheory.DRFil.isDR_of_spans T K' LL _ fun y => ?_
    obtain ⟨m, b, d, hm, e⟩ := hs y
    exact ⟨m, b, d, fun i => ddR_le h ρ (hm i), e⟩
  · intro hd
    exact GlobalTheory.DRFil.isDR_of_spans T K LL ρ (GlobalTheory.DRFil.spans_descent l P K K' LL h V ρ
      ((GlobalTheory.DRFil.filSpans T K' LL _ hd).spans _))

/- English proof (translation)
Introduce `_ _ _ _ T _ _ _ h _ _ _ _ _ _ ρ` and use `⟨isCrys_restrict h ρ T, isDR_restrict_iff h ρ T⟩`.
-/
theorem restrict_crys_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      (IsCrys (P.PD K) ρ → IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) ∧
        (IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
  fun _ _ _ _ T _ _ _ h _ _ _ _ _ _ ρ => ⟨isCrys_restrict h ρ T, isDR_restrict_iff h ρ T⟩

end GlobalTheory.Per.TiedRestrict
