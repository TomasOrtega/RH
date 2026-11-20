import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PPointIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsMultiHomogIdeal ptsIntegral pot segre mcPts SameOrbit
  segre_smul mcPts_smul sameOrbit_of_segre)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents segreChartIdeal chartLift
  chartLift_segre_apply mem_segreChartComponents)

namespace SegreChartIntegralPoints

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aeval_eq_eval' {m : ℕ} (x : Fin m → ℂ) (p : MvPolynomial (Fin m) ℂ) : aeval x p = eval x p := rfl

/- English proof (translation)
The claim follows from `RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C _⟩`.
-/
theorem ker_eval_isMaximal {m : ℕ} (x : Fin m → ℂ) :
    (RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C _⟩

/- English proof (translation)
Establish `hle : ∀ x ∈ S, (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) ≤ RingHom.ker (eval x)` using `fun x hx p hp => by rw [RingHom.mem_ker, ← aeval_eq_eval']; exact hp x hx`. Establish `hinf : hS.toFinset.inf (fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)) ≤ (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ))`. Introduce `p hp`. Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `x hx`.

Use `Finset.inf_le (f := fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)) (hS.mem_toFinset.2 hx) hp` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, ← aeval_eq_eval']`. Then use the resulting hypothesis. Establish `hcont : ∀ q : Ideal (MvPolynomial (Fin m) ℂ), q.IsPrime → vanishingIdeal ℂ S ≤ q → ∃ x ∈ S, RingHom.ker (eval x) ≤ q` using `fun q hq hIq => by`. Take `⟨x, hx, hxq⟩` from `(hq.inf_le' (s := hS.toFinset)).1 (hinf.trans hIq)`. Conclude with `⟨x, hS.mem_toFinset.1 hx, hxq⟩`.

Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce `hq`. Take `⟨x, hx, hxq⟩` from `hcont q hq.1.1 hq.1.2`. Conclude with `⟨x, hx, le_antisymm hxq (hq.2 ⟨RingHom.ker_isPrime _, hle x hx⟩ hxq)⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨⟨RingHom.ker_isPrime _, hle x hx⟩, fun q hq hqx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyq⟩` from `hcont q hq.1 hq.2`. Establish `hxy` using `(ker_eval_isMaximal y).eq_of_le (ker_eval_isMaximal x).ne_top (hyq.trans hqx)`. Use `show RingHom.ker (eval x) ≤ q`.

Rewrite using `[← hxy]`. Conclude with `hyq`.
-/
theorem minimalPrimes_vanishingIdeal {m : ℕ} {S : Set (Fin m → ℂ)} (hS : S.Finite) :
    (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)).minimalPrimes =
      (fun x => RingHom.ker (eval x)) '' S := by
  classical
  have hle : ∀ x ∈ S, (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) ≤ RingHom.ker (eval x) :=
    fun x hx p hp => by rw [RingHom.mem_ker, ← aeval_eq_eval']; exact hp x hx
  have hinf : hS.toFinset.inf (fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)) ≤
      (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) := by
    intro p hp
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have := Finset.inf_le (f := fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ))
      (hS.mem_toFinset.2 hx) hp
    rwa [RingHom.mem_ker, ← aeval_eq_eval'] at this

  have hcont : ∀ q : Ideal (MvPolynomial (Fin m) ℂ), q.IsPrime → vanishingIdeal ℂ S ≤ q →
      ∃ x ∈ S, RingHom.ker (eval x) ≤ q := fun q hq hIq => by
    obtain ⟨x, hx, hxq⟩ := (hq.inf_le' (s := hS.toFinset)).1 (hinf.trans hIq)
    exact ⟨x, hS.mem_toFinset.1 hx, hxq⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ := hcont q hq.1.1 hq.1.2
    exact ⟨x, hx, le_antisymm hxq (hq.2 ⟨RingHom.ker_isPrime _, hle x hx⟩ hxq)⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨RingHom.ker_isPrime _, hle x hx⟩, fun q hq hqx => ?_⟩
    obtain ⟨y, hy, hyq⟩ := hcont q hq.1 hq.2
    have hxy := (ker_eval_isMaximal y).eq_of_le (ker_eval_isMaximal x).ne_top (hyq.trans hqx)
    show RingHom.ker (eval x) ≤ q
    rw [← hxy]
    exact hyq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `choose j hj using hz`. Introduce `h`. Establish `h0 : segre z j = 0` using `by rw [h]; rfl`. Conclude with `Finset.prod_ne_zero_iff.2 (fun k _ => hj k) h0`.
-/
theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) : segre z ≠ 0 := by
  choose j hj using hz
  intro h
  have h0 : segre z j = 0 := by rw [h]; rfl
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hj k) h0

/- English proof (translation)
Set `c : K → ℂ` to `fun k => if k = k₀ then (segre t i)⁻¹ else 1`. Apply the tactic sequence `have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, hi]`. Establish `hprod : ∏ k, c k = (segre t i)⁻¹`. Rewrite using `[Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]`. Simplify using `[c]`.

Conclude with `⟨_, mcPts_smul hP c hc ht, ⟨c, hc, rfl⟩, by rw [segre_smul, hprod]⟩`.
-/
theorem exists_normalised {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (k₀ : K) (i : (k : K) → ι k)
    {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P) (hi : segre t i ≠ 0) :
    ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' = (segre t i)⁻¹ • segre t := by
  classical
  let c : K → ℂ := fun k => if k = k₀ then (segre t i)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, hi]
  have hprod : ∏ k, c k = (segre t i)⁻¹ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
    simp [c]
  exact ⟨_, mcPts_smul hP c hc ht, ⟨c, hc, rfl⟩, by rw [segre_smul, hprod]⟩

/- English proof (translation)
Introduce `K _ _ ι _ P m σ i L g δ G Φ hP hg hδ hvan hG`. Take `⟨k₀⟩` from `hP.1`. Take `⟨R, hRm, hRu, hRint⟩` from `Inter.regularityPointsSum_holds.proof K ι P hP`. Establish `horb : ∀ z z', SameOrbit z z' → g z = g z'`. Introduce and unpack `z z' ⟨c, hc, rfl⟩`.

Conclude with `hg.2 c z' hc`. Establish `hL : pot L = (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)` using `Subsingleton.elim _ _`. Rewrite using `[hL, hRint g fun z z' _ h => horb z z' h]`. Use `set S := R.filter (fun t => segre t i ≠ 0) with hS`. Set `ν : ((Σ k, ι k) → ℂ) → Fin m → ℂ` to `fun t a => (segre t i)⁻¹ * segre t (σ a)`.

Establish `hν : ∀ t ∈ S, ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' i = 1 ∧ ν t = fun a => segre t' (σ a)`. Introduce `t ht`. Take `⟨htR, hti⟩` from `Finset.mem_filter.1 ht`. Take `⟨t', ht'm, ht'o, ht's⟩` from `exists_normalised hP.2.1.2.1 k₀ i (hRm t htR) hti`. Use `⟨t', ht'm, ht'o, ?_, funext fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[ht's, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hti]`. Rewrite using `[ht's, Pi.smul_apply, smul_eq_mul]`. Establish `hchart : segreChartSet P σ i = ν '' S`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, hzi, rfl⟩`. Take `⟨t, ⟨htR, c, hc, rfl⟩, -⟩` from `hRu z hz`. Establish `hzs : segre (fun p => c p.1 * t p) = (∏ k, c k) • segre t` using `segre_smul c t`. Establish `h1 : (∏ k, c k) * segre t i = 1`. Rewrite using `[← hzi, hzs, Pi.smul_apply, smul_eq_mul]`.

Establish `hti : segre t i ≠ 0` using `right_ne_zero_of_mul_eq_one h1`. Use `⟨t, Finset.mem_filter.2 ⟨htR, hti⟩, funext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hzs, Pi.smul_apply, smul_eq_mul, eq_inv_of_mul_eq_one_left h1]`. Introduce and unpack `⟨t, ht, rfl⟩`. Take `⟨t', ht'm, -, ht'i, hνt⟩` from `hν t ht`.

Conclude with `⟨t', ht'm, ht'i, hνt⟩`. Establish `hinj : Set.InjOn ν S`. Introduce `t₁ ht₁ t₂ ht₂ h`. Take `⟨ht₁R, ht₁i⟩` from `Finset.mem_filter.1 ht₁`. Take `⟨ht₂R, ht₂i⟩` from `Finset.mem_filter.1 ht₂`.

Establish `hseg : segre t₁ = (segre t₁ i * (segre t₂ i)⁻¹) • segre t₂`. Use function extensionality and compare the values at `j`. Establish `hj` using `congrFun h (σ.symm j)`. Simplify using `only [ν, Equiv.apply_symm_apply] at hj`. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_assoc, ← hj, ← mul_assoc, mul_inv_cancel₀ ht₁i, one_mul]`.

Establish `h12` using `sameOrbit_of_segre (hRm t₂ ht₂R).1 _ (mul_ne_zero ht₁i (inv_ne_zero ht₂i)) hseg`. Conclude with `(hRu t₁ (hRm t₁ ht₁R)).unique ⟨ht₁R, fun _ => 1, fun _ => one_ne_zero, by simp⟩ ⟨ht₂R, h12⟩`. Establish `hfin : (segreChartSet P σ i).Finite` using `hchart ▸ S.finite_toSet.image ν`. Establish `hfs : hfin.toFinset = S.image ν` using `Finset.coe_injective (by simp [hchart])`. Establish `hcomp : segreChartComponents P σ i = hfin.toFinset.image (fun x => RingHom.ker (eval x))`.

Use extensionality with `J`. Rewrite using `[mem_segreChartComponents, segreChartIdeal, minimalPrimes_vanishingIdeal hfin]`. Simplify using the standard rewrite rules. Establish `hkinj : ∀ x y : Fin m → ℂ, RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ) = RingHom.ker (eval y) → x = y` using `fun x y h => by`. Use `PointIntegral.zeroSet_ker_eval x` as an intermediate fact.

Rewrite `this` using `[h, PointIntegral.zeroSet_ker_eval]`. Conclude with `(Set.singleton_eq_singleton_iff.1 this).symm`. Rewrite using `[hcomp, Finset.sum_image fun x _ y _ h => hkinj x y h]`. Rewrite using `[Finset.sum_congr rfl fun x _ => PointIntegral.proof m x G Φ]`. Rewrite using `[hfs, Finset.sum_image hinj]`.

Rewrite using `[← Finset.sum_filter_of_ne (p := fun t => segre t i ≠ 0) fun t ht hgt hti => hgt (hvan t (by`. Rewrite using `[hti, norm_zero]`. Conclude with `mul_pos hδ (norm_pos_iff.2 (segre_ne_zero (hRm t ht).1))))]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Take `⟨t', ht'm, ht'o, ht'i, hνt⟩` from `hν t ht`.

Establish `hx : ν t ∈ segreChartSet P σ i` using `hchart ▸ Set.mem_image_of_mem ν ht`. Rewrite using `[(hG _ hx).eq_of_nhds, Function.comp_apply, ← horb t' t ht'o, hνt]`. Establish `hne : ∀ k, t' ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`. Establish `h1 : segre t' i = 0` using `Finset.prod_eq_zero (f := fun k => t' ⟨k, i k⟩) (Finset.mem_univ k) h0`. Rewrite `h1` using `[ht'i]`.

Conclude with `one_ne_zero h1`. Establish `hlift : chartLift σ i (fun a => segre t' (σ a)) = fun p => (t' ⟨p.1, i p.1⟩)⁻¹ * t' p`. Use function extensionality and compare the values at `⟨k, j⟩`. Rewrite using `[chartLift_segre_apply σ i t' ht'i k j, mul_comm]`. Rewrite using `[hlift]`.

Conclude with `(hg.2 (fun k => (t' ⟨k, i k⟩)⁻¹) t' fun k => inv_ne_zero (hne k)).symm`.
-/
theorem proof : SegreChartIntegralPoints.Statement := by
  classical
  intro K _ _ ι _ P m σ i L g δ G Φ hP hg hδ hvan hG
  obtain ⟨k₀⟩ := hP.1
  obtain ⟨R, hRm, hRu, hRint⟩ := Inter.regularityPointsSum_holds.proof K ι P hP
  have horb : ∀ z z', SameOrbit z z' → g z = g z' := by
    rintro z z' ⟨c, hc, rfl⟩
    exact hg.2 c z' hc
  have hL : pot L = (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := Subsingleton.elim _ _
  rw [hL, hRint g fun z z' _ h => horb z z' h]
  set S := R.filter (fun t => segre t i ≠ 0) with hS
  let ν : ((Σ k, ι k) → ℂ) → Fin m → ℂ := fun t a => (segre t i)⁻¹ * segre t (σ a)

  have hν : ∀ t ∈ S, ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' i = 1 ∧
      ν t = fun a => segre t' (σ a) := by
    intro t ht
    obtain ⟨htR, hti⟩ := Finset.mem_filter.1 ht
    obtain ⟨t', ht'm, ht'o, ht's⟩ := exists_normalised hP.2.1.2.1 k₀ i (hRm t htR) hti
    refine ⟨t', ht'm, ht'o, ?_, funext fun a => ?_⟩
    · rw [ht's, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hti]
    · rw [ht's, Pi.smul_apply, smul_eq_mul]
  have hchart : segreChartSet P σ i = ν '' S := by
    ext x
    constructor
    · rintro ⟨z, hz, hzi, rfl⟩
      obtain ⟨t, ⟨htR, c, hc, rfl⟩, -⟩ := hRu z hz
      have hzs : segre (fun p => c p.1 * t p) = (∏ k, c k) • segre t := segre_smul c t
      have h1 : (∏ k, c k) * segre t i = 1 := by
        rw [← hzi, hzs, Pi.smul_apply, smul_eq_mul]
      have hti : segre t i ≠ 0 := right_ne_zero_of_mul_eq_one h1
      refine ⟨t, Finset.mem_filter.2 ⟨htR, hti⟩, funext fun a => ?_⟩
      rw [hzs, Pi.smul_apply, smul_eq_mul, eq_inv_of_mul_eq_one_left h1]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨t', ht'm, -, ht'i, hνt⟩ := hν t ht
      exact ⟨t', ht'm, ht'i, hνt⟩
  have hinj : Set.InjOn ν S := by
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ht₁R, ht₁i⟩ := Finset.mem_filter.1 ht₁
    obtain ⟨ht₂R, ht₂i⟩ := Finset.mem_filter.1 ht₂
    have hseg : segre t₁ = (segre t₁ i * (segre t₂ i)⁻¹) • segre t₂ := by
      funext j
      have hj := congrFun h (σ.symm j)
      simp only [ν, Equiv.apply_symm_apply] at hj
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, ← hj, ← mul_assoc, mul_inv_cancel₀ ht₁i, one_mul]
    have h12 := sameOrbit_of_segre (hRm t₂ ht₂R).1 _ (mul_ne_zero ht₁i (inv_ne_zero ht₂i)) hseg
    exact (hRu t₁ (hRm t₁ ht₁R)).unique ⟨ht₁R, fun _ => 1, fun _ => one_ne_zero, by simp⟩ ⟨ht₂R, h12⟩
  have hfin : (segreChartSet P σ i).Finite := hchart ▸ S.finite_toSet.image ν
  have hfs : hfin.toFinset = S.image ν := Finset.coe_injective (by simp [hchart])
  have hcomp : segreChartComponents P σ i = hfin.toFinset.image (fun x => RingHom.ker (eval x)) := by
    ext J
    rw [mem_segreChartComponents, segreChartIdeal, minimalPrimes_vanishingIdeal hfin]
    simp
  have hkinj : ∀ x y : Fin m → ℂ, RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ) = RingHom.ker (eval y) →
      x = y := fun x y h => by
    have := PointIntegral.zeroSet_ker_eval x
    rw [h, PointIntegral.zeroSet_ker_eval] at this
    exact (Set.singleton_eq_singleton_iff.1 this).symm
  rw [hcomp, Finset.sum_image fun x _ y _ h => hkinj x y h]
  rw [Finset.sum_congr rfl fun x _ => PointIntegral.proof m x G Φ]
  rw [hfs, Finset.sum_image hinj]

  rw [← Finset.sum_filter_of_ne (p := fun t => segre t i ≠ 0) fun t ht hgt hti => hgt (hvan t (by
    rw [hti, norm_zero]
    exact mul_pos hδ (norm_pos_iff.2 (segre_ne_zero (hRm t ht).1))))]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨t', ht'm, ht'o, ht'i, hνt⟩ := hν t ht
  have hx : ν t ∈ segreChartSet P σ i := hchart ▸ Set.mem_image_of_mem ν ht
  rw [(hG _ hx).eq_of_nhds, Function.comp_apply, ← horb t' t ht'o, hνt]
  have hne : ∀ k, t' ⟨k, i k⟩ ≠ 0 := fun k h0 => by
    have h1 : segre t' i = 0 := Finset.prod_eq_zero (f := fun k => t' ⟨k, i k⟩) (Finset.mem_univ k) h0
    rw [ht'i] at h1
    exact one_ne_zero h1
  have hlift : chartLift σ i (fun a => segre t' (σ a)) = fun p => (t' ⟨p.1, i p.1⟩)⁻¹ * t' p := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i t' ht'i k j, mul_comm]
  rw [hlift]
  exact (hg.2 (fun k => (t' ⟨k, i k⟩)⁻¹) t' fun k => inv_ne_zero (hne k)).symm

end SegreChartIntegralPoints

end GroundTheory.Heights₂.Heights.Targets
