import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlacesGood

variable {D : D7}

/- English proof (translation)
Establish `h : P ∈ (D.ntw.pD i : Set (Pl D.host.E))` using `hP`. Rewrite `h` using `[D.ntw.pD_eq i]`. Use `split_ifs at h`. Conclude with `⟨_, Or.inr rfl, h⟩`. Conclude with `⟨_, Or.inl rfl, h⟩`.
-/
theorem over_pde_of_mem_pD (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h : P ∈ (D.ntw.pD i : Set (Pl D.host.E)) := hP
  rw [D.ntw.pD_eq i] at h
  split_ifs at h
  · exact ⟨_, Or.inr rfl, h⟩
  · exact ⟨_, Or.inl rfl, h⟩

/- English proof (translation)
The claim follows from `(h (n : 𝓞 D.host.E) (n : 𝓞 D.host.E) (by simp)).1 hn`.
-/
theorem natCast_mem_of_conj {P P' : Pl D.host.E} (h : IsConjPl D.host P P') {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal :=
  (h (n : 𝓞 D.host.E) (n : 𝓞 D.host.E) (by simp)).1 hn

/- English proof (translation)
Establish `e` using `GlobalTheory.HostSplit.ncard_placesOver D.host.E hp`. Rewrite `e` using `[h]`. Conclude with `e`.
-/
theorem splitsC_of_primesOver {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
  have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
  rw [h] at e
  exact e

/- English proof (translation)
The claim follows from `Nat.Coprime.mul_left (UpperTheory.Ram.coprime_QSq D.host hp hs hq) (D.host.ccK_coprime p (by simp [hl]))`.
-/
theorem coprime_of_level {p : ℕ} (hp : p.Prime) (hs : p ∉ D.host.small) (hq : p ≠ D.host.q) (hl : p ∈ D.host.levelPrimes) :
    Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p :=
  Nat.Coprime.mul_left (UpperTheory.Ram.coprime_QSq D.host hp hs hq)
    (D.host.ccK_coprime p (by simp [hl]))

/- English proof (translation)
The claim follows from `GlobalTheory.HalfCompare.primeToAA_of_not_mem (GlobalTheory.HalfCompare.not_mem_of_coprime P hc hp)`.
-/
theorem count_AA_eq_zero {P : Pl D.host.E} {p : ℕ} (hc : Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p)
    (hp : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : FractionalIdeal.count D.host.E P D.host.AA = 0 :=
  GlobalTheory.HalfCompare.primeToAA_of_not_mem (GlobalTheory.HalfCompare.not_mem_of_coprime P hc hp)

/- English proof (translation)
Introduce `D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL hsp hq i ch hch`. Establish `hPg : ∀ P ∈ Rl.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Rl.C.P.Div k P` using `fun P hP => by`. Take `⟨k, hk⟩` from `(hL.Pg P).1 hP`. Conclude with `⟨k, GlobalTheory.Mem.TypePl.div_over Rl.C.P hk, hk⟩`. Establish `hQ : ∀ P ∈ half ch (D.ntw.pD i), ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `fun P hP => over_pde_of_mem_pD i (mem_half.1 hP).1`.

Establish `hsm : ∀ p : ℕ, p.Prime → GlobalTheory.Mem.Chr.SplitsC D.host.E p → p ∉ D.host.small` using `fun p hp h hs => UpperTheory.Ram.not_dvd_condN_of_unram D.host hp (fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p hp h w hw).2.1) (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)`. Establish `hpp : ∀ p, (p = D.host.pde ∨ p = D.host.pde') → p.Prime ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E p ∧ Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p ∧ ∀ k, p ≠ D.host.g k`. Introduce and unpack `p (rfl | rfl)`. Conclude with `⟨D.host.pde_prime, splitsC_of_primesOver D.host.pde_prime hsp.1, coprime_of_level D.host.pde_prime (hsm _ D.host.pde_prime (splitsC_of_primesOver D.host.pde_prime hsp.1)) hq.1 D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1⟩`. Conclude with `⟨D.host.pde'_prime, splitsC_of_primesOver D.host.pde'_prime hsp.2, coprime_of_level D.host.pde'_prime (hsm _ D.host.pde'_prime (splitsC_of_primesOver D.host.pde'_prime hsp.2)) hq.2 D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2⟩`.

Use `⟨⟨Rl.Pg ∪ half ch (D.ntw.pD i), Finset.subset_union_left, Finset.subset_union_right, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.UnivGood.splitSet_of_split (fun P hP => ?_) fun P hP P' hP' hc => ?_` and prove the remaining obligations. Break down `Finset.mem_union.1 hP with hP | hP` into its components or cases. Take `⟨k, hk, -⟩` from `hPg P hP`. Conclude with `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1`.

Take `⟨p, hp, hm⟩` from `hQ P hP`. Conclude with `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1`. Apply the tactic sequence `rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'`. Take `⟨k, hk, hd⟩` from `hPg P hP`. Take `⟨k', hk', hd'⟩` from `hPg P' hP'`.

Establish `e` using `GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (D.host.g_prime k) (D.host.g_prime k') (natCast_mem_of_conj hc hk) hk'`. Establish `hkk : k = k'`. Use `D.host.g_ne` as an intermediate fact. Apply the tactic sequence `fin_cases k <;> fin_cases k' <;> simp_all`. Substitute `hkk` using the available equality.

Conclude with `GlobalTheory.Mem.TypePl.not_isConjPl Rl.C.P (D.nd.g_split k) hd hd' hc`. Take `⟨k, hk, -⟩` from `hPg P hP`. Take `⟨p, hp, hm⟩` from `hQ P' hP'`. Conclude with `(hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) hm (natCast_mem_of_conj hc hk))`. Take `⟨p, hp, hm⟩` from `hQ P hP`.

Take `⟨k, hk, -⟩` from `hPg P' hP'`. Conclude with `(hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) (natCast_mem_of_conj hc hm) hk)`. Take `⟨p, hp, hm⟩` from `hQ P hP`. Establish `hs` using `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1`. Conclude with `(hch.pair P P' hc (ne_of_split hs hc)).1 (mem_half.1 hP).2 (mem_half.1 hP').2`.

Use `Finset.disjoint_left.2 fun P hP hP' => ?_` and prove the remaining obligations. Take `⟨k, hk, -⟩` from `hPg P hP`. Take `⟨p, hp, hm⟩` from `hQ P hP'`. Conclude with `(hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P (hpp p hp).1 (D.host.g_prime k) hm hk)`. Introduce `PP hPP PP' hPP'`.

Establish `hmem : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal` using `fun n hn => by`. Break down `hPP' with rfl | hc` into its components or cases. Conclude with `hn`. Conclude with `GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc hn`. Break down `hPP with hPP | hPP` into its components or cases.

Take `⟨k, hk, -⟩` from `hPg PP hPP`. Conclude with `count_AA_eq_zero (GlobalTheory.CoverHalf.g_coprime D k).symm (hmem _ hk)`. Take `⟨p, hp, hm⟩` from `hQ PP hPP`. Conclude with `count_AA_eq_zero (hpp p hp).2.2.1 (hmem _ hm)`.
-/
theorem placesOK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL hsp hq i ch hch
  classical
  have hPg : ∀ P ∈ Rl.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Rl.C.P.Div k P := fun P hP => by
    obtain ⟨k, hk⟩ := (hL.Pg P).1 hP
    exact ⟨k, GlobalTheory.Mem.TypePl.div_over Rl.C.P hk, hk⟩
  have hQ : ∀ P ∈ half ch (D.ntw.pD i), ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => over_pde_of_mem_pD i (mem_half.1 hP).1
  have hsm : ∀ p : ℕ, p.Prime → GlobalTheory.Mem.Chr.SplitsC D.host.E p → p ∉ D.host.small := fun p hp h hs =>
    UpperTheory.Ram.not_dvd_condN_of_unram D.host hp (fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p hp h w hw).2.1)
      (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  have hpp : ∀ p, (p = D.host.pde ∨ p = D.host.pde') → p.Prime ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E p ∧
      Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p ∧ ∀ k, p ≠ D.host.g k := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, splitsC_of_primesOver D.host.pde_prime hsp.1,
        coprime_of_level D.host.pde_prime (hsm _ D.host.pde_prime (splitsC_of_primesOver D.host.pde_prime hsp.1)) hq.1 D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1⟩
    · exact ⟨D.host.pde'_prime, splitsC_of_primesOver D.host.pde'_prime hsp.2,
        coprime_of_level D.host.pde'_prime (hsm _ D.host.pde'_prime (splitsC_of_primesOver D.host.pde'_prime hsp.2)) hq.2 D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2⟩
  refine ⟨⟨Rl.Pg ∪ half ch (D.ntw.pD i), Finset.subset_union_left, Finset.subset_union_right, ?_⟩, ?_, ?_⟩
  · refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => ?_) fun P hP P' hP' hc => ?_
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨k, hk, -⟩ := hPg P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
    · rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨k, hk, hd⟩ := hPg P hP
        obtain ⟨k', hk', hd'⟩ := hPg P' hP'
        have e := GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (D.host.g_prime k) (D.host.g_prime k') (natCast_mem_of_conj hc hk) hk'
        have hkk : k = k' := by
          have := D.host.g_ne
          fin_cases k <;> fin_cases k' <;> simp_all
        subst hkk
        exact GlobalTheory.Mem.TypePl.not_isConjPl Rl.C.P (D.nd.g_split k) hd hd' hc
      · obtain ⟨k, hk, -⟩ := hPg P hP
        obtain ⟨p, hp, hm⟩ := hQ P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) hm (natCast_mem_of_conj hc hk))
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        obtain ⟨k, hk, -⟩ := hPg P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) (natCast_mem_of_conj hc hm) hk)
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        have hs := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
        exact (hch.pair P P' hc (ne_of_split hs hc)).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    obtain ⟨k, hk, -⟩ := hPg P hP
    obtain ⟨p, hp, hm⟩ := hQ P hP'
    exact (hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P (hpp p hp).1 (D.host.g_prime k) hm hk)
  · intro PP hPP PP' hPP'
    have hmem : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := fun n hn => by
      rcases hPP' with rfl | hc
      · exact hn
      · exact GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc hn
    rcases hPP with hPP | hPP
    · obtain ⟨k, hk, -⟩ := hPg PP hPP
      exact count_AA_eq_zero (GlobalTheory.CoverHalf.g_coprime D k).symm (hmem _ hk)
    · obtain ⟨p, hp, hm⟩ := hQ PP hPP
      exact count_AA_eq_zero (hpp p hp).2.2.1 (hmem _ hm)

end GlobalTheory.SeriesTie.PlacesGood

end
