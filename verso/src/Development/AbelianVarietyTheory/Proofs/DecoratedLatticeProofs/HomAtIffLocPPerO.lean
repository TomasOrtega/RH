import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HomAtPer

/- English proof (translation)
Use `haveI := P.isPrime`. Establish `: Finite (𝓞 D.host.E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Establish `hl : (ringChar (𝓞 D.host.E ⧸ P.asIdeal)).Prime` using `CharP.char_is_prime (𝓞 D.host.E ⧸ P.asIdeal) _`. Establish `hlP : ((ringChar (𝓞 D.host.E ⧸ P.asIdeal) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `CharP.cast_eq_zero _ _`. Establish `h2 : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `fun h => hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_right _ h))`. Establish `hq : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `fun h => hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ h))`. Conclude with `GlobalTheory.AAUnitAway.exists_den D P.asIdeal hl (UpperTheory.Ram.notMem_small_of_QS_notMem D.host hlP h2) (fun e => hq (e ▸ hlP)) hlP`.
-/
theorem exists_den_away (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ z : 𝓞 D.host.E, z ∉ P.asIdeal ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * z := by
  haveI := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hl : (ringChar (𝓞 D.host.E ⧸ P.asIdeal)).Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ P.asIdeal) _
  have hlP : ((ringChar (𝓞 D.host.E ⧸ P.asIdeal) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
  have h2 : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_right _ h))
  have hq : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ h))
  exact GlobalTheory.AAUnitAway.exists_den D P.asIdeal hl (UpperTheory.Ram.notMem_small_of_QS_notMem D.host hlP h2)
    (fun e => hq (e ▸ hlP)) hlP

/- English proof (translation)
Introduce `D S T SS hSS N N' hN _hN' x`. Prove the components needed by the constructor for the conclusion. Introduce `hx P hP haveI := P.isPrime`. Take `⟨gens, hgens⟩` from `hN.1.fg`. Establish `hden : ∀ g ∈ gens, ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x g ∈ N'`.

Introduce `g hg`. Establish `hg' : g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N` using `⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul, ← hgens]; exact Submodule.subset_span hg⟩`. Take `⟨s, hs, hsx⟩` from `hx P hP g hg'`. Conclude with `⟨s, hs, hsx⟩`. Use `choose! sg hsg using hden`.

Use `set s : 𝓞 D.host.E := ∏ g ∈ gens, sg g with hs`. Establish `hsP : s ∉ P.asIdeal`. Rewrite using `[hs]`. Introduce `hm`. Take `⟨g, hg, hgP⟩` from `Ideal.IsPrime.prod_mem_iff.1 hm`.

Conclude with `(hsg g hg).1 hgP`. Establish `hsx : s • x ∈ homO N N'`. Introduce `y hy`. Rewrite `hy` using `[← hgens]`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem g hg`. Establish `e : (s • x) g = (∏ g' ∈ gens.erase g, sg g') • (sg g • x g)`. Rewrite using `[LinearMap.smul_apply, smul_smul, hs, ← Finset.mul_prod_erase gens sg hg, mul_comm]`. Rewrite using `[e]`. Conclude with `N'.smul_mem _ (hsg g hg).2`.

Consider the case `zero => rw [map_zero]`. Conclude with `N'.zero_mem`. Consider the case `add y z _ _ h1 h2 => rw [map_add]`. Conclude with `N'.add_mem h1 h2`. Consider the case `smul o y _ h => rw [LinearMap.map_smul_of_tower]`.

Conclude with `N'.smul_mem _ h`. Conclude with `⟨s, hsP, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, s • x, hsx, (one_smul _ _).symm⟩⟩`. Introduce `hx P hP y hy haveI := P.isPrime`. Take `⟨z, hz, hden⟩` from `exists_den_away D P (hSS P hP)`. Take `⟨s, hs, hsx⟩` from `hx P hP`.

Take `⟨t, ht, hty⟩` from `hy`. Establish `hper : ∀ w ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∀ v ∈ N, (z • w) v ∈ N'`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w h`.

Take `⟨r, hr, h0, hh0, rfl⟩` from `h`. Introduce `v hv`. Take `⟨ρ, hρ⟩` from `hden r hr`. Establish `e : (z • r • h0) v = ρ • h0 v`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul D.host.E z, ← algebraMap_smul D.host.E ρ, smul_smul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `(z : D.host.E) * r = (ρ : D.host.E)`. Rewrite using `[hρ, mul_comm]`. Rewrite using `[e]`. Conclude with `N'.smul_mem ρ (hh0 v hv)`.

Consider the case `zero => intro v _`. Rewrite using `[smul_zero, LinearMap.zero_apply]`. Conclude with `N'.zero_mem`. Consider the case `add w₁ w₂ _ _ h1 h2 => intro v hv`. Rewrite using `[smul_add, LinearMap.add_apply]`.

Conclude with `N'.add_mem (h1 v hv) (h2 v hv)`. Consider the case `smul r w₁ _ h1 => intro v hv`. Rewrite using `[smul_comm, LinearMap.smul_apply]`. Conclude with `N'.smul_mem r (h1 v hv)`. Use `⟨z * s * t, P.asIdeal.primeCompl.mul_mem (P.asIdeal.primeCompl.mul_mem hz hs) ht, ?_⟩` and prove the remaining obligations.

Establish `e : (z * s * t) • x y = (z • s • x) (t • y)`. Rewrite using `[LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hper _ hsx _ hty`.
-/
theorem homAt_iff_locP_perO : ∀ (D : D7) (S T : HSp D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, x ∈ Formalism.L2.Col.homAt SS N N' ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D S T SS hSS N N' hN _hN' x
  constructor
  · intro hx P hP
    haveI := P.isPrime
    obtain ⟨gens, hgens⟩ := hN.1.fg
    have hden : ∀ g ∈ gens, ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x g ∈ N' := by
      intro g hg
      have hg' : g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
        ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul, ← hgens]; exact Submodule.subset_span hg⟩
      obtain ⟨s, hs, hsx⟩ := hx P hP g hg'
      exact ⟨s, hs, hsx⟩
    choose! sg hsg using hden
    set s : 𝓞 D.host.E := ∏ g ∈ gens, sg g with hs
    have hsP : s ∉ P.asIdeal := by
      rw [hs]
      intro hm
      obtain ⟨g, hg, hgP⟩ := Ideal.IsPrime.prod_mem_iff.1 hm
      exact (hsg g hg).1 hgP
    have hsx : s • x ∈ homO N N' := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        have e : (s • x) g = (∏ g' ∈ gens.erase g, sg g') • (sg g • x g) := by
          rw [LinearMap.smul_apply, smul_smul, hs, ← Finset.mul_prod_erase gens sg hg, mul_comm]
        rw [e]; exact N'.smul_mem _ (hsg g hg).2
      | zero => rw [map_zero]; exact N'.zero_mem
      | add y z _ _ h1 h2 => rw [map_add]; exact N'.add_mem h1 h2
      | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h
    exact ⟨s, hsP, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, s • x, hsx, (one_smul _ _).symm⟩⟩
  · intro hx P hP y hy
    haveI := P.isPrime
    obtain ⟨z, hz, hden⟩ := exists_den_away D P (hSS P hP)
    obtain ⟨s, hs, hsx⟩ := hx P hP
    obtain ⟨t, ht, hty⟩ := hy
    have hper : ∀ w ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∀ v ∈ N, (z • w) v ∈ N' := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨r, hr, h0, hh0, rfl⟩ := h
        intro v hv
        obtain ⟨ρ, hρ⟩ := hden r hr
        have e : (z • r • h0) v = ρ • h0 v := by
          rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul D.host.E z, ← algebraMap_smul D.host.E ρ, smul_smul]
          congr 1
          change (z : D.host.E) * r = (ρ : D.host.E)
          rw [hρ, mul_comm]
        rw [e]; exact N'.smul_mem ρ (hh0 v hv)
      | zero => intro v _; rw [smul_zero, LinearMap.zero_apply]; exact N'.zero_mem
      | add w₁ w₂ _ _ h1 h2 => intro v hv; rw [smul_add, LinearMap.add_apply]; exact N'.add_mem (h1 v hv) (h2 v hv)
      | smul r w₁ _ h1 => intro v hv; rw [smul_comm, LinearMap.smul_apply]; exact N'.smul_mem r (h1 v hv)
    refine ⟨z * s * t, P.asIdeal.primeCompl.mul_mem (P.asIdeal.primeCompl.mul_mem hz hs) ht, ?_⟩
    have e : (z * s * t) • x y = (z • s • x) (t • y) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul]
      congr 1; ring
    rw [e]
    exact hper _ hsx _ hty

end GlobalTheory.HomAtPer
