import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.VacOffS

variable {D : D7}

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `(Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some`. Conclude with `⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩`.
-/
theorem exists_under (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set M : ℕ := NS * NT with hMdef`. Establish `hM0 : (M : D.host.F) ≠ 0`. Introduce `h`. Apply `hv` to reduce the goal to its premises. Establish `: (M : 𝓞 D.host.F) = 0`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `using h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hval : HeightOneSpectrum.valuation D.host.F v (M : D.host.F) = 1`.

Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 hv`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨γ, hγ, rfl⟩ : ∃ γ ∈ intAf D.host.F, α = algebraMap D.host.F _ (M : D.host.F) * γ := by`.

Use `⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Use `mul_mem (hα w) ?_` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀, hval, inv_one]`. Rewrite using `[hP w hw, zero_mul]`. Conclude with `zero_mem _`. Rewrite using `[mul_comm α, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]`. Establish `hs' : s ∈ L0c D S` using `by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hs`.

Establish `ht' : t ∈ L0c D T` using `by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact ht`. Use `AddSubgroup.subset_closure ⟨γ, hγ, fun w hw => (hw trivial).elim, a, ha, _, hS s hs', _, hT t ht', ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[GlobalTheory.VacLat.pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]`.

Use `congr 1`. Rewrite using `[Algebra.smul_def, map_natCast, hMdef]`. Simplify using `only [star_mul', star_natCast, Nat.cast_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latO_at_le {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {NS NT : ℕ}
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ LS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ LT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E)) (fun u => u = v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set M : ℕ := NS * NT with hMdef
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hv
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  have hval : HeightOneSpectrum.valuation D.host.F v (M : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ intAf D.host.F, α = algebraMap D.host.F _ (M : D.host.F) * γ := by
    refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
    · rw [map_mul, AlgHom.commutes]
      by_cases hw : w = v
      · subst hw
        refine mul_mem (hα w) ?_
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀, hval, inv_one]
      · rw [hP w hw, zero_mul]; exact zero_mem _
    · rw [mul_comm α, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]
  have hs' : s ∈ L0c D S := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hs
  have ht' : t ∈ L0c D T := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact ht
  refine AddSubgroup.subset_closure ⟨γ, hγ, fun w hw => (hw trivial).elim, a, ha, _, hS s hs', _, hT t ht', ?_⟩
  ext i j
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.VacLat.pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  congr 1
  rw [Algebra.smul_def, map_natCast, hMdef]
  simp only [star_mul', star_natCast, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.ChainOnto.VacOffS

open GlobalTheory.ChainOnto.VacOffS in

/- English proof (translation)
Introduce `D _ c hc k _ s s' hs hs' p hp φ v hv`. Take `⟨ξ, f₀, hf₀, e, he, hth⟩` from `hp.vec`. Take `⟨NS, hNS, hNSv⟩` from `hs.base`. Take `⟨NT, hNT, hNTv⟩` from `hs'.base`. Take `⟨hr, ξ', hL⟩` from `hs.lev`.

Establish `hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal`. Take `⟨P, hP⟩` from `exists_under (D := D) v`. Establish `hPv : P.under (𝓞 D.host.F) ∉ c.S` using `by rw [hP]; exact hv`. Establish `h1` using `hNSv P hPv`. Establish `h2` using `hNTv P hPv`.

Introduce `h`. Rewrite `h` using `[← hP]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h`. Rewrite `h` using `[map_natCast, Nat.cast_mul]`. Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases.

Conclude with `h1 h`. Conclude with `h2 h`. Establish `hle` using `latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM`. Establish `hoff : ∀ PP ∈ s.L.Pg ∪ ∅, PP.under (𝓞 D.host.F) ≠ v`. Introduce `PP hPP h0`.

Rewrite `hPP` using `[Finset.union_empty, hL]`. Conclude with `hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)`. Establish `hfix : ∀ u ∈ latO s.V s'.V (frameLat s.V : Set (Fin s.V.rank → D.host.E)) (frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v), heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ` using `fun u hu h0 => GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u (GlobalTheory.VacGood.infPart_latO (hle hu)) (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul …`. Use `⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩` and prove the remaining obligations. Conclude with `hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))`.

Conclude with `hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)`.
-/
theorem GlobalTheory.ChainOnto.fock_vacFin_off :
    ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D _ c hc k _ s s' hs hs' p hp φ v hv
  classical
  obtain ⟨ξ, f₀, hf₀, e, he, hth⟩ := hp.vec
  obtain ⟨NS, hNS, hNSv⟩ := hs.base
  obtain ⟨NT, hNT, hNTv⟩ := hs'.base
  obtain ⟨hr, ξ', hL⟩ := hs.lev
  have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    obtain ⟨P, hP⟩ := exists_under (D := D) v
    have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
    have h1 := hNSv P hPv
    have h2 := hNTv P hPv
    intro h
    rw [← hP] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact h1 h
    · exact h2 h
  have hle := latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
  have hoff : ∀ PP ∈ s.L.Pg ∪ ∅, PP.under (𝓞 D.host.F) ≠ v := by
    intro PP hPP h0
    rw [Finset.union_empty, hL] at hPP
    exact hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hfix : ∀ u ∈ latO s.V s'.V (frameLat s.V : Set (Fin s.V.rank → D.host.E))
      (frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
      heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
        (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
  refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
  · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)

end
