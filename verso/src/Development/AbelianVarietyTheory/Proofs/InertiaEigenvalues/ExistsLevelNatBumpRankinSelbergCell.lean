import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)`. Rewrite `h` using `[v.valuation_of_algebraMap]`. Simplify using `using h`.
-/
theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

/- English proof (translation)
Use `set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq`. Establish `hq0 : ∀ w, q w ≠ ⊥` using `fun w h => by`. Establish `hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w`. Rewrite using `[hq, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem _`.

Rewrite `hm` using `[h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot hm`. Use `set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞`. Use `set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn`. Establish `hspan : Ideal.span {n} = 𝔞` using `Ideal.span_singleton_generator 𝔞`.

Establish `h𝔞0 : 𝔞 ≠ ⊥`. Rewrite using `[h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Conclude with `fun w _ => hq0 w`. Establish `hn0 : n ≠ 0` using `fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])`. Use `set N₀ : ℕ := n.natAbs with hN₀`.

Establish `hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w` using `fun w hw => by`. Establish `h1 : (N₀ : ℤ) ∈ 𝔞`. Rewrite using `[← hspan, Ideal.mem_span_singleton]`. Conclude with `Int.dvd_natAbs.2 dvd_rfl`. Conclude with `Ideal.prod_le_inf.trans (Finset.inf_le hw) h1`.

Use `⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩` and prove the remaining obligations. Establish `h1 : (N₀ : 𝓞 E) ∈ v.asIdeal`. Use `hN₀q v hv` as an intermediate fact. Rewrite `this` using `[hq, Ideal.mem_comap, map_natCast]`. Then use the resulting hypothesis. Rewrite using `[Nat.cast_pow]`.

Conclude with `Ideal.pow_mem_pow h1 k`. Rewrite `h` using `[Nat.cast_pow]`. Establish `h1 : (N₀ : 𝓞 E) ∈ v.asIdeal` using `v.isPrime.mem_of_pow_mem k h`. Establish `h2 : (N₀ : ℤ) ∈ q v` using `by rwa [hq, Ideal.mem_comap, map_natCast]`. Establish `h3 : n ∈ q v`.

Take `⟨c, hc⟩` from `(Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ h2`. Use `haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _`. Establish `h4 : 𝔞 ≤ q v` using `by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3`.

Take `⟨w, hw, hle⟩` from `(Ideal.IsPrime.prod_le hp).1 h4`. Establish `hmax : (q w).IsMaximal` using `(Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)`. Establish `heq : q w = q v` using `hmax.eq_of_le hp.ne_top hle`. Conclude with `hv (hS w hw v heq.symm)`.
-/
theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [IsTotallyComplex E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ v`. Express the relevant statement in the definitionally equal form `Valued.v ((N : v.adicCompletion E) * y v) ≤ _`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))`.

Introduce `h set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc`. Establish `hcN : c * (N : Af E) = 1`. Rewrite using `[hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]`. Use `⟨z * c, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : c v * (N : v.adicCompletion E) = 1` using `congrArg (fun x : Af E => x v) hcN`.

Establish `e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1` using `by rw [← map_mul, e, map_one]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Express the relevant statement in the definitionally equal form `Valued.v (z v * c v) ≤ 1`. Rewrite using `[map_mul, ← e', mul_comm (Valued.v (c v))]`. Conclude with `mul_le_mul_of_nonneg_right (h v) zero_le'`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams

open GlobalTheory.RSParams in

/- English proof (translation)
Introduce `E _ _ _ m S hS V hV hw`. Take `⟨J, hJS, -, hJV⟩` from `GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw`. Use `set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk`. Take `⟨N, hN, hNS, hNc⟩` from `exists_nat S hS k`. Establish `hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1` using `fun v => by`.

Rewrite using `[valued_natCast]`. Conclude with `v.intValuation_le_one _`. Establish `hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))` using `fun v hv => by`. Rewrite using `[valued_natCast]`. Use `((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)` and prove the remaining obligations.

Establish `h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤ ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ)` using `Int.self_le_toNat _`. Establish `h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k` using `Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat) (fun _ _ => Nat.zero_le _) hv`. Use linear arithmetic over natural numbers and integers. Establish `hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1` using `fun v hv => by`. Rewrite using `[valued_natCast]`.

Conclude with `le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))`. Establish `he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m)` using `fun w => by`. Simplify using the standard rewrite rules. Take `⟨ρ, hts, hcs, hcd, hr, h1⟩` from `exists_contDiff_tsupport_subset (n := ⊤) ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)`. Establish `hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1` using `fun u => hr ⟨u, rfl⟩`.

Use `⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩, by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz …` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `((mem_natLat_iff hN z).1 hz v).trans (hv1 v)`. Conclude with `((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)`. Rewrite using `[mem_natLat_iff hN, mem_natLat_iff hN]`.

Use `forall_congr' fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hzz v hv]`. Rewrite using `[hvn v hv]`. Conclude with `⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv), fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩`.
-/
theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
