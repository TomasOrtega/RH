import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeRingLaurent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsMultiHomogIdeal divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat segreChartIdeal segreChartComponents
  mem_segreChartComponents)

namespace ChartConeLength

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`. Consider the case `mul_X p q hp => rw [map_mul, map_mul, hp, aeval_X]`.
-/
theorem aeval_algebraMap_X (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X q)) f =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
      MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p q hp => rw [map_mul, map_mul, hp, aeval_X]

/- English proof (translation)
Use `⟨∏ k, (isUnit_coneX i k).unit⁻¹ ^ a k, ?_⟩` and prove the remaining obligations. Establish `h` using `ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hf (fun k => (((isUnit_coneX i k).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i)) (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X q))`. Rewrite `h` using `[aeval_algebraMap_X]`. Rewrite using `[coneRatio, h]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem coneRatio_eq_unit_mul (i : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : ReciprocityTheory.AnForm.R.IsMultiHomog f a) :
    ∃ c : (ConeRing i)ˣ, coneRatio i f = c * algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) f := by
  refine ⟨∏ k, (isUnit_coneX i k).unit⁻¹ ^ a k, ?_⟩
  have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hf
    (fun k => (((isUnit_coneX i k).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i))
    (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X q))
  rw [aeval_algebraMap_X] at h
  rw [coneRatio, h]
  push_cast
  rfl

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hQ`. Establish `key : ∀ f ∈ S, ∃ c : (ConeRing i)ˣ, ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f)) = c * algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f)`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Rewrite using `[ratioMap_dehom]`.

Conclude with `coneRatio_eq_unit_mul i (a := a) fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k`. Rewrite using `[Ideal.map_span, Ideal.map_span, Ideal.map_span, Ideal.map_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨f, hf, rfl⟩, rfl⟩`.

Take `⟨c, hc⟩` from `key f hf`. Establish `h : algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f) = ((c⁻¹ : (ConeRing i)ˣ) : ConeRing i) * ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f))`. Rewrite using `[hc, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[h]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩)`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩`. Take `⟨c, hc⟩` from `key f hf`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨f, hf, rfl⟩, rfl⟩)`.
-/
theorem map_algebraMap_eq_map_ratioMap (i : (k : K) → ι k) {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q) :
    (Q.map (MvPolynomial.map (Int.castRingHom ℂ))).map (algebraMap _ (ConeRing i)) =
      ((Q.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have key : ∀ f ∈ S, ∃ c : (ConeRing i)ˣ,
      ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f)) =
        c * algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    rw [ratioMap_dehom]
    exact coneRatio_eq_unit_mul i (a := a) fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k
  rw [Ideal.map_span, Ideal.map_span, Ideal.map_span, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := key f hf
    have h : algebraMap _ (ConeRing i) (MvPolynomial.map (Int.castRingHom ℂ) f) =
        ((c⁻¹ : (ConeRing i)ˣ) : ConeRing i) * ratioMap i (dehom i (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
      rw [hc, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := key f hf
    rw [hc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨f, hf, rfl⟩, rfl⟩)

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `le_antisymm (fun g hg => ?_) Ideal.le_comap_map` and prove the remaining obligations. Establish `h` using `Ideal.mem_map_of_mem (evalOne i) (Ideal.mem_comap.1 hg)`. Rewrite `h` using `[Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_ratioMap]`. Then use the resulting hypothesis.
-/
theorem comap_ratioMap_map (i : (k : K) → ι k) (Y : Ideal (DehomRing i)) :
    (Y.map (ratioMap i)).comap (ratioMap i) = Y := by
  refine le_antisymm (fun g hg => ?_) Ideal.le_comap_map
  have h := Ideal.mem_map_of_mem (evalOne i) (Ideal.mem_comap.1 hg)
  rwa [Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_ratioMap] at h

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce and unpack `g ⟨n, hn⟩`. Establish `h1 : ratioMap i g ∈ (P'.map (algebraMap _ (ConeRing i))).radical` using `⟨n, by rw [← map_pow, heq]; exact Ideal.mem_map_of_mem _ hn⟩`. Rewrite `h1` using `[← IsLocalization.map_radical (Submonoid.powers (coneUnit i)) (ConeRing i), hrad.radical, heq]`. Rewrite using `[← comap_ratioMap_map i (P'.map (dehom i))]`. Conclude with `h1`.
-/
theorem isRadical_map_dehom (i : (k : K) → ι k) {P' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hrad : P'.IsRadical)
    (heq : P'.map (algebraMap _ (ConeRing i)) = (P'.map (dehom i)).map (ratioMap i)) :
    (P'.map (dehom i)).IsRadical := by
  rintro g ⟨n, hn⟩
  have h1 : ratioMap i g ∈ (P'.map (algebraMap _ (ConeRing i))).radical :=
    ⟨n, by rw [← map_pow, heq]; exact Ideal.mem_map_of_mem _ hn⟩
  rw [← IsLocalization.map_radical (Submonoid.powers (coneUnit i)) (ConeRing i), hrad.radical, heq] at h1
  rw [← comap_ratioMap_map i (P'.map (dehom i))]
  exact h1

omit [Fintype K] in

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hP`. Use `⟨S ∪ {s}, ?_, by rw [Ideal.span_union]⟩` and prove the remaining obligations. Introduce and unpack `f (hf | hf)`. Conclude with `hS f hf`. Rewrite using `[Set.mem_singleton_iff.1 hf]`.

Conclude with `⟨a, hs⟩`.
-/
theorem isMultiHomogIdeal_sup_span {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {s : MRing ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S ∪ {s}, ?_, by rw [Ideal.span_union]⟩
  rintro f (hf | hf)
  · exact hS f hf
  · rw [Set.mem_singleton_iff.1 hf]
    exact ⟨a, hs⟩

end ChartConeLength

open ChartConeLength in

/- English proof (translation)
Introduce `K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle`. Establish `hρ : Function.Surjective (segreDehom σ i)` using `segreDehom_surjective σ i`. Take `⟨hTf, hTp⟩` from `hT K ι i`. Establish `hWa` using `(divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh`. Establish `hPm : IsMultiHomogIdeal P` using `hP.2.1.2.1`.

Establish `hWm : IsMultiHomogIdeal W` using `hWa.2.1.2.1`. Take `⟨a, -, hsa, -⟩` from `hs`. Establish `hJm : IsMultiHomogIdeal (P ⊔ Ideal.span {s})` using `isMultiHomogIdeal_sup_span hPm hsa`. Establish `hPrad : ((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).IsRadical` using `isRadical_map_dehom i (HilbertSamuel.PrimeComplexRadical.proof _ P hP.2.1.1) (map_algebraMap_eq_map_ratioMap i hPm)`. Establish `hIP` using `hN K ι P m σ i hPm`.

Rewrite `hIP` using `[hPrad.radical]`. Establish `hIW` using `hN K ι W m σ i hWm`. Establish `hker : ∀ J : Ideal (DehomRing i), RingHom.ker (segreDehom σ i) ≤ J.comap (segreDehom σ i)` using `fun J => Ideal.comap_mono bot_le`. Establish `hLHS : segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s} = (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).comap (segreDehom σ i)`. Establish `hJy : ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) = (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).map (segreDehom σ i)`.

Rewrite using `[Ideal.map_sup, Ideal.map_sup, Ideal.map_sup, hIP, Ideal.map_comap_of_surjective _ hρ, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, Set.image_singleton, chartSection_eq_chartSubst, segreDehom_chartSubst]`. Rewrite using `[hJy, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]`. Conclude with `le_sup_of_le_left (hIP ▸ hker _)`. Take `⟨Q, hQ⟩ : ∃ Q, Q = W'.map (segreDehom σ i)` from `⟨_, rfl⟩`. Establish `hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes` using `mem_segreChartComponents.1 hW'`.

Establish `: W'.IsPrime` using `hW'min.1.1`. Establish `hkerW' : RingHom.ker (segreDehom σ i) ≤ W'` using `le_trans (hIW ▸ hker _) hW'min.1.2`. Establish `hW'Q : W' = Q.comap (segreDehom σ i)`. Rewrite using `[hQ, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]`. Conclude with `hkerW'`.

Establish `hQp : Q.IsPrime` using `hQ ▸ Ideal.map_isPrime_of_surjective hρ hkerW'`. Establish `hQmin : Q ∈ ((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).minimalPrimes`. Establish `hWyQ : (W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) ≤ Q`. Rewrite using `[hQ]`. Introduce `g hg`.

Take `⟨f, rfl⟩` from `hρ g`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Apply `hW'min.1.2` to reduce the goal to its premises. Rewrite using `[hIW]`. Conclude with `Ideal.le_radical hg`.

Use `⟨⟨hQp, hWyQ⟩, fun q hq hqQ => ?_⟩` and prove the remaining obligations. Establish `: q.IsPrime` using `hq.1`. Establish `hc : W' ≤ q.comap (segreDehom σ i)` using `hW'min.2 ⟨Ideal.comap_isPrime _ _, by rw [hIW]; exact Ideal.comap_mono ((Ideal.IsPrime.radical_le_iff hq.1).2 hq.2)⟩ (by rw [hW'Q]; exact Ideal.comap_mono hqQ)`. Rewrite using `[hQ]`. Conclude with `(Ideal.map_mono hc).trans Ideal.map_comap_le`.

Establish `hL : localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' = localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q`. Rewrite using `[hLHS, hW'Q]`. Conclude with `LocalMultComap.proof _ _ (segreDehom σ i : MvPolynomial (Fin m) ℂ →+* DehomRing i) _ Q hρ hQp`. Establish `: W''.IsPrime` using `hW''.1.1`. Establish `hu : coneUnit i ∉ W''`.

Introduce `hu`. Establish `h1 : segreDehom σ i (chartSubst σ i (coneUnit i)) ∈ Q`. Rewrite using `[hQ]`. Conclude with `Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) hu))`. Rewrite `h1` using `[segreDehom_chartSubst, dehom_coneUnit]`.

Conclude with `hQp.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Establish `hdisj : Disjoint (Submonoid.powers (coneUnit i) : Set (MvPolynomial (Σ k, ι k) ℂ)) W''` using `(Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).2 hu`. Establish `h𝔓p : (W''.map (algebraMap _ (ConeRing i))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) W'' ‹_› hdisj`. Establish `h𝔓u : (W''.map (algebraMap _ (ConeRing i))).under _ = W''` using `IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) ‹_› hdisj`. Establish `h𝔓min : W''.map (algebraMap _ (ConeRing i)) ∈ (((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i)).minimalPrimes`.

Rewrite using `[← map_algebraMap_eq_map_ratioMap i hWm, IsLocalization.minimalPrimes_map (Submonoid.powers (coneUnit i)) (ConeRing i), Set.mem_preimage, h𝔓u]`. Conclude with `hW''`. Establish `: ((W''.map (algebraMap _ (ConeRing i))).comap (ratioMap i)).IsPrime` using `Ideal.comap_isPrime _ _`. Take `⟨q₀, hq₀min, hq₀le⟩` from `Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.1 h𝔓min.1.2)`. Establish `hq₀p : q₀.IsPrime` using `hq₀min.1.1`.

Establish `hq₀e : W''.map (algebraMap _ (ConeRing i)) = q₀.map (ratioMap i)` using `le_antisymm (h𝔓min.2 ⟨hTp q₀ hq₀p, Ideal.map_mono hq₀min.1.2⟩ (Ideal.map_le_iff_le_comap.2 hq₀le)) (Ideal.map_le_iff_le_comap.2 hq₀le)`. Establish `hq₀ : q₀ = W''.map (dehom i)`. Establish `h` using `congrArg (Ideal.map (evalOne i)) hq₀e`. Rewrite `h` using `[Ideal.map_map, Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_comp_algebraMap]`. Conclude with `h.symm`.

Establish `hq₀Q : q₀ = Q`. Establish `hle' : q₀ ≤ Q`. Rewrite using `[hq₀, Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, ← segreDehom_chartSubst σ i f, hQ]`.

Conclude with `Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) hf))`. Conclude with `le_antisymm hle' (hQmin.2 ⟨hq₀p, hq₀min.1.2⟩ hle')`. Establish `hflat1 : localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (algebraMap _ (ConeRing i))) (W''.map (algebraMap _ (ConeRing i))) = localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W''`. Establish `: (W''.map (algebraMap _ (ConeRing i))).LiesOver W''` using `⟨h𝔓u.symm⟩`. Establish `: Module.Flat (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i)` using `IsLocalization.flat _ (Submonoid.powers (coneUnit i))`.

Conclude with `localMult_map_of_flat _ W'' _ (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)`. Establish `hflat2 : localMult ((((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i)) (Q.map (ratioMap i)) = localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q`. Set `` to `(ratioMap i).toAlgebra`. Establish `: Module.Flat (DehomRing i) (ConeRing i)` using `hTf`. Use `hTp Q hQp` as an intermediate fact.

Establish `: (Q.map (algebraMap (DehomRing i) (ConeRing i))).LiesOver Q` using `⟨(comap_ratioMap_map i Q).symm⟩`. Conclude with `localMult_map_of_flat _ Q (Q.map (algebraMap (DehomRing i) (ConeRing i))) (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)`. Rewrite using `[hL, ← hflat2, ← hq₀Q, ← hq₀e, ← map_algebraMap_eq_map_ratioMap i hJm, hflat1]`.
-/
theorem ChartConeLength.proof (hT : ConeRingLaurent.Statement) (hN : ChartDehomIdeal.Statement) :
    ChartConeLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle
  classical
  have hρ : Function.Surjective (segreDehom σ i) := segreDehom_surjective σ i
  obtain ⟨hTf, hTp⟩ := hT K ι i
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have hPm : IsMultiHomogIdeal P := hP.2.1.2.1
  have hWm : IsMultiHomogIdeal W := hWa.2.1.2.1
  obtain ⟨a, -, hsa, -⟩ := hs
  have hJm : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := isMultiHomogIdeal_sup_span hPm hsa
  have hPrad : ((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).IsRadical :=
    isRadical_map_dehom i (HilbertSamuel.PrimeComplexRadical.proof _ P hP.2.1.1) (map_algebraMap_eq_map_ratioMap i hPm)
  have hIP := hN K ι P m σ i hPm
  rw [hPrad.radical] at hIP
  have hIW := hN K ι W m σ i hWm

  have hker : ∀ J : Ideal (DehomRing i), RingHom.ker (segreDehom σ i) ≤ J.comap (segreDehom σ i) := fun J =>
    Ideal.comap_mono bot_le
  have hLHS : segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s} =
      (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).comap (segreDehom σ i) := by
    have hJy : ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) =
        (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).map (segreDehom σ i) := by
      rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_sup, hIP, Ideal.map_comap_of_surjective _ hρ, Ideal.map_span,
        Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, Set.image_singleton,
        chartSection_eq_chartSubst, segreDehom_chartSubst]
    rw [hJy, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]
    exact le_sup_of_le_left (hIP ▸ hker _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.map (segreDehom σ i) := ⟨_, rfl⟩
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hW'min.1.1
  have hkerW' : RingHom.ker (segreDehom σ i) ≤ W' := le_trans (hIW ▸ hker _) hW'min.1.2
  have hW'Q : W' = Q.comap (segreDehom σ i) := by
    rw [hQ, Ideal.comap_map_of_surjective _ hρ, eq_comm, sup_eq_left]
    exact hkerW'
  have hQp : Q.IsPrime := hQ ▸ Ideal.map_isPrime_of_surjective hρ hkerW'
  have hQmin : Q ∈ ((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).minimalPrimes := by
    have hWyQ : (W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i) ≤ Q := by
      rw [hQ]
      intro g hg
      obtain ⟨f, rfl⟩ := hρ g
      apply Ideal.mem_map_of_mem
      apply hW'min.1.2
      rw [hIW]
      exact Ideal.le_radical hg
    refine ⟨⟨hQp, hWyQ⟩, fun q hq hqQ => ?_⟩
    have : q.IsPrime := hq.1
    have hc : W' ≤ q.comap (segreDehom σ i) := hW'min.2
      ⟨Ideal.comap_isPrime _ _, by rw [hIW]; exact Ideal.comap_mono ((Ideal.IsPrime.radical_le_iff hq.1).2 hq.2)⟩
      (by rw [hW'Q]; exact Ideal.comap_mono hqQ)
    rw [hQ]
    exact (Ideal.map_mono hc).trans Ideal.map_comap_le
  have hL : localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
      localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q := by
    rw [hLHS, hW'Q]
    exact LocalMultComap.proof _ _ (segreDehom σ i : MvPolynomial (Fin m) ℂ →+* DehomRing i) _ Q hρ hQp

  have : W''.IsPrime := hW''.1.1
  have hu : coneUnit i ∉ W'' := by
    intro hu
    have h1 : segreDehom σ i (chartSubst σ i (coneUnit i)) ∈ Q := by
      rw [hQ]
      exact Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+*
        MvPolynomial (Fin m) ℂ) hu))
    rw [segreDehom_chartSubst, dehom_coneUnit] at h1
    exact hQp.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hdisj : Disjoint (Submonoid.powers (coneUnit i) : Set (MvPolynomial (Σ k, ι k) ℂ)) W'' :=
    (Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).2 hu
  have h𝔓p : (W''.map (algebraMap _ (ConeRing i))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) W'' ‹_› hdisj
  have h𝔓u : (W''.map (algebraMap _ (ConeRing i))).under _ = W'' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (coneUnit i)) (ConeRing i) ‹_› hdisj
  have h𝔓min : W''.map (algebraMap _ (ConeRing i)) ∈
      (((W.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).map (ratioMap i)).minimalPrimes := by
    rw [← map_algebraMap_eq_map_ratioMap i hWm,
      IsLocalization.minimalPrimes_map (Submonoid.powers (coneUnit i)) (ConeRing i), Set.mem_preimage, h𝔓u]
    exact hW''
  have : ((W''.map (algebraMap _ (ConeRing i))).comap (ratioMap i)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q₀, hq₀min, hq₀le⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.1 h𝔓min.1.2)
  have hq₀p : q₀.IsPrime := hq₀min.1.1
  have hq₀e : W''.map (algebraMap _ (ConeRing i)) = q₀.map (ratioMap i) :=
    le_antisymm (h𝔓min.2 ⟨hTp q₀ hq₀p, Ideal.map_mono hq₀min.1.2⟩ (Ideal.map_le_iff_le_comap.2 hq₀le))
      (Ideal.map_le_iff_le_comap.2 hq₀le)
  have hq₀ : q₀ = W''.map (dehom i) := by
    have h := congrArg (Ideal.map (evalOne i)) hq₀e
    rw [Ideal.map_map, Ideal.map_map, evalOne_comp_ratioMap, Ideal.map_id, evalOne_comp_algebraMap] at h
    exact h.symm
  have hq₀Q : q₀ = Q := by
    have hle' : q₀ ≤ Q := by
      rw [hq₀, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, ← segreDehom_chartSubst σ i f, hQ]
      exact Ideal.mem_map_of_mem _ (hle (Ideal.mem_map_of_mem (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+*
        MvPolynomial (Fin m) ℂ) hf))
    exact le_antisymm hle' (hQmin.2 ⟨hq₀p, hq₀min.1.2⟩ hle')

  have hflat1 : localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map
      (algebraMap _ (ConeRing i))) (W''.map (algebraMap _ (ConeRing i))) =
      localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W'' := by
    have : (W''.map (algebraMap _ (ConeRing i))).LiesOver W'' := ⟨h𝔓u.symm⟩
    have : Module.Flat (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) :=
      IsLocalization.flat _ (Submonoid.powers (coneUnit i))
    exact localMult_map_of_flat _ W'' _ (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)
  have hflat2 : localMult ((((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map
      (dehom i)).map (ratioMap i)) (Q.map (ratioMap i)) =
      localMult (((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)) Q := by
    let := (ratioMap i).toAlgebra
    have : Module.Flat (DehomRing i) (ConeRing i) := hTf
    have := hTp Q hQp
    have : (Q.map (algebraMap (DehomRing i) (ConeRing i))).LiesOver Q := ⟨(comap_ratioMap_map i Q).symm⟩
    exact localMult_map_of_flat _ Q (Q.map (algebraMap (DehomRing i) (ConeRing i)))
      (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)
  rw [hL, ← hflat2, ← hq₀Q, ← hq₀e, ← map_algebraMap_eq_map_ratioMap i hJm, hflat1]

end GroundTheory.Heights₂.Heights.Targets
