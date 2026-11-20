import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormEqOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqNcardPrimesOver

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitChoice

/- English proof (translation)
Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible`. Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)`. Establish `hm : ((p : ℕ) : 𝓞 K) ∈ Q`. Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K))` using `hQc ▸ Ideal.mem_span_singleton_self _`. Simplify using `using this`.

Use `⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩` and prove the remaining obligations. Rewrite `hm` using `[h0, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hm)`.
-/
theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩
  rw [h0, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

/- English proof (translation)
Introduce `hmem`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Establish `hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal)` using `(Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)`. Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))`. Simplify using `only [eq_intCast, Int.cast_natCast] at hab`.

Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))`.
-/
theorem natCast_notMem_of_absNorm_lt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (h : Ideal.absNorm v.asIdeal < p) : (p : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at hab
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc`. Establish `hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely`. Rewrite using `[GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]`. Conclude with `⟨hp, fun w hw => ⟨h3 w hw, (GlobalTheory.SplitResidue.residue_and_unramified D.host.E p hp hs w hw).2⟩⟩`.
-/
theorem splitsCompletely_of_modEq_one (D : D7) {p : ℕ} (hp : p.Prime)
    (hc : p ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]) : SplitsCompletely D p := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely
    rw [GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]
  exact ⟨hp, fun w hw => ⟨h3 w hw, (GlobalTheory.SplitResidue.residue_and_unramified D.host.E p hp hs w hw).2⟩⟩

/- English proof (translation)
Introduce `D S N hS hN`. Establish `hn : D.host.QS ≠ 0` using `D.host.QS_pos.ne'`. Establish `hq : D.host.q ≠ 0` using `D.host.hyp.1.ne_zero`. Establish `hd : D.host.d ≠ 0` using `D.host.hyp.2.1.ne_zero`. Establish `hm : D.host.QS * D.host.q * D.host.d ≠ 0` using `by positivity`.

Take `⟨p, hp, hlt, hc⟩` from `Nat.exists_prime_gt_modEq_one (N + ∑ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal) hm`. Use `⟨p, splitsCompletely_of_modEq_one D hp hc, ?_, fun v hv => ?_, exists_place_over _ hp⟩` and prove the remaining obligations. Use `(Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_` and prove the remaining obligations. Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdv` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `natCast_notMem_of_absNorm_lt v hp ?_` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun v : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm v.asIdeal) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hv)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_split_prime : ∀ (D : D7) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (N : ℕ), S.Finite → N ≠ 0 →
    ∃ p : ℕ, SplitsCompletely D p ∧ p.Coprime N ∧ (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) ∧
      ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D S N hS hN
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one
    (N + ∑ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal) hm
  refine ⟨p, splitsCompletely_of_modEq_one D hp hc, ?_, fun v hv => ?_, exists_place_over _ hp⟩
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdv
    omega
  · refine natCast_notMem_of_absNorm_lt v hp ?_
    have := Finset.single_le_sum (f := fun v : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hv)
    omega

end GlobalTheory.SplitChoice
