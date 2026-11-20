import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeOfIsIdemAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

open scoped Pointwise

noncomputable section

namespace GlobalTheory.ModulInter

/- English proof (translation)
Establish `hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F)` using `GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)`. Unfold `Places.modulBar Places.modul`. Rewrite using `[Finset.smul_prod']`. Use `IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_` and prove the remaining obligations. Rewrite using `[smul_pow']`.

Use `IsCoprime.pow ?_` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Establish `hm : (D.host.conj • (P.w v').asIdeal).IsMaximal`. Use `(P.w v').isPrime` as an intermediate fact. Use `Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_` and prove the remaining obligations.

Use `congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0` as an intermediate fact. Simplify using `using this`. Use `Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_` and prove the remaining obligations. Establish `hvv : v = v'`. Establish `a` using `congrArg HeightOneSpectrum.asIdeal (P.under_w hv)`.

Establish `b` using `congrArg HeightOneSpectrum.asIdeal (P.under_w hv')`. Use `HeightOneSpectrum.ext ?_` and prove the remaining obligations. Rewrite using `[← a, ← b]`. Use `show Ideal.under _ _ = Ideal.under _ _`. Rewrite using `[heq, hF]`.

Substitute `hvv` using the available equality. Take `⟨e, he⟩` from `P.w_split v hv`. Conclude with `GlobalTheory.FunObj.StdDatum.conj_smul_ne_of_isIdemAt he heq.symm`.
-/
theorem modul_isCoprime_conj {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) :
    IsCoprime (P.modul sc) (P.modulBar sc) := by
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold Places.modulBar Places.modul
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact GlobalTheory.FunObj.StdDatum.conj_smul_ne_of_isIdemAt he heq.symm

/- English proof (translation)
Establish `h` using `GlobalTheory.SeeSaw.idV_incA_mul (algebraMap (𝓞 D.host.E) D.host.E m) _ v hs`. Use `GlobalTheory.SeeSaw.idV_mono ?_ v h` and prove the remaining obligations. Establish `hI0 : ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 hI`. Establish `hle : FractionalIdeal.spanSingleton _ (algebraMap (𝓞 D.host.E) D.host.E m) ≤ ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)`. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem]`.

Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem incA_mul_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (𝔞 : GlobalTheory.SeeSaw.FI D) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥)
    {m : 𝓞 D.host.E} (hm : m ∈ I) {s : AE D}
    (hs : s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v) :
    incA D (algebraMap (𝓞 D.host.E) D.host.E m) * s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have h := GlobalTheory.SeeSaw.idV_incA_mul (algebraMap (𝓞 D.host.E) D.host.E m) _ v hs
  refine GlobalTheory.SeeSaw.idV_mono ?_ v h
  have hI0 : ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have hle : FractionalIdeal.spanSingleton _ (algebraMap (𝓞 D.host.E) D.host.E m) ≤
      ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩
  calc FractionalIdeal.spanSingleton _ (algebraMap (𝓞 D.host.E) D.host.E m) * (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)
      ≤ ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) * (𝔞 * ((I : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) :=
        by gcongr
    _ = 𝔞 := by rw [mul_left_comm, mul_inv_cancel₀ hI0, mul_one]

/- English proof (translation)
Introduce `D T L P sc v 𝔞 s h1 h2`. Establish `hsup` using `(Ideal.isCoprime_iff_sup_eq).1 (modul_isCoprime_conj P sc)`. Take `⟨m, hm, m', hm', hmm⟩` from `Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.modul sc ⊔ P.modulBar sc)`. Establish `a1` using `incA_mul_mem v 𝔞 _ (P.modul_ne_bot sc) hm h1`. Establish `a2` using `incA_mul_mem v 𝔞 _ (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot P sc) hm' h2`.

Establish `e : s = incA D (algebraMap (𝓞 D.host.E) D.host.E m) * s + incA D (algebraMap (𝓞 D.host.E) D.host.E m') * s`. Rewrite using `[← add_mul, ← map_add, ← map_add, hmm, map_one, map_one, one_mul]`. Rewrite using `[e]`. Conclude with `add_mem a1 a2`.
-/
theorem mem_idV_of_inter : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D) (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v 𝔞 s h1 h2
  have hsup := (Ideal.isCoprime_iff_sup_eq).1 (modul_isCoprime_conj P sc)
  obtain ⟨m, hm, m', hm', hmm⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.modul sc ⊔ P.modulBar sc)
  have a1 := incA_mul_mem v 𝔞 _ (P.modul_ne_bot sc) hm h1
  have a2 := incA_mul_mem v 𝔞 _ (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot P sc) hm' h2
  have e : s = incA D (algebraMap (𝓞 D.host.E) D.host.E m) * s + incA D (algebraMap (𝓞 D.host.E) D.host.E m') * s := by
    rw [← add_mul, ← map_add, ← map_add, hmm, map_one, map_one, one_mul]
  rw [e]
  exact add_mem a1 a2

end GlobalTheory.ModulInter
