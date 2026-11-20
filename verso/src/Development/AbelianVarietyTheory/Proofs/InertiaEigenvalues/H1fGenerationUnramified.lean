import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.GenCountUnram

/- English proof (translation)
Introduce `D l _ K LL`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound`. Introduce `hbij T hT`. Establish `ht` using `D.locT l`. Establish `hgood` using `(GlobalTheory.LocalIntegers.good_integers l LL).1`.

Establish `h27` using `GlobalTheory.T.h1fT_span_card_bound l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood T`. Establish `hDR` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) ht K LL T.V T.ρ hT).1`. Establish `hgen` using `h27 hDR`. Take `⟨s, hs, hcard⟩` from `hgen`. Set `A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `⟨T.V, T.ρ, T.cont⟩`.

Establish `hseq0` using `GlobalTheory.SeqDim.h1f_finrank l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood A`. Establish `hseq` using `(hseq0 hDR).2`. Establish `hdR0` using `GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) ht K LL T.V T.ρ`. Use `haveI := hdR0.1`. Establish `hdR` using `hdR0.2`.

Establish `hK : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K)` using `(AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij).toLinearEquiv.finrank_eq.symm`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite `hdR` using `[hK]`. Establish `hle : finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ ⊓ FilV ((D.loc l).PD K) (LL` using `↥LL.1) (V := T.V) 0) ≤ finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ) := Submodule.finrank_mono inf_le_left`. Establish `hmul : finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V + finrank ↥LL.1 T.V = (finrank ℚ_[l] ↥(K0 K) + 1) * finrank ↥LL.1 T.V` using `by ring`.

Rewrite using `[← hmul]`. Use `zify at hcard hdR hle ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem admGenL_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  intro D l _ K LL
  unfold Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound
  intro hbij T hT
  have ht := D.locT l
  have hgood := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have h27 := GlobalTheory.T.h1fT_span_card_bound l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood T
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) ht K LL T.V T.ρ hT).1
  have hgen := h27 hDR
  obtain ⟨s, hs, hcard⟩ := hgen
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := ⟨T.V, T.ρ, T.cont⟩
  have hseq0 := GlobalTheory.SeqDim.h1f_finrank l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood A
  have hseq := (hseq0 hDR).2
  have hdR0 := GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) ht K LL T.V T.ρ
  haveI := hdR0.1
  have hdR := hdR0.2
  have hK : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij).toLinearEquiv.finrank_eq.symm
  refine ⟨s, hs, ?_⟩
  rw [hK] at hdR
  have hle : finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0)
      ≤ finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ) := Submodule.finrank_mono inf_le_left
  have hmul : finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V + finrank ↥LL.1 T.V
      = (finrank ℚ_[l] ↥(K0 K) + 1) * finrank ↥LL.1 T.V := by ring
  rw [← hmul]
  zify at hcard hdR hle ⊢
  linarith

end GlobalTheory.GenCountUnram
