import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory Filter Topology Matrix SheetLift CxInt
open ReciprocityTheory.ChartRestriction.G.Geo (segre_differentiableAt)

section Count

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)`. Rewrite using `[lift_segre i0 k0 hne]`. Apply the tactic sequence `refine ⟨cone_scale hP (c := fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩`. Establish `hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]`.

Conclude with `div_self hne`. Rewrite using `[segre_bsmul, hprod]`. Use function extensionality and compare the values at `i`. Rewrite using `[one_mul]`.
-/
theorem cone_lift_spec [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ conePts Q ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨cone_scale hP (c := fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩)
    (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]

/- English proof (translation)
Take `⟨hd0, ⟨z0, hz0, hs0⟩, -⟩` from `hev.self_of_nhds`. Break down `isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩` into its components or cases. Use `⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩` and prove the remaining obligations. Establish `hzz : z0 = z` using `funext fun p => (IsEmpty.false p.1).elim`. Use `⟨differentiableAt_const _, hzz ▸ hz, ?_⟩` and prove the remaining obligations.

Use `show Ψ (segre z0) = _`. Rewrite using `[hzz, hs]`. Conclude with `hΨ`. Use `choose i0 hi0 using hz0.1`. Establish `hy : h y i0 ≠ 0`.

Rewrite using `[← hs0]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k`. Establish `hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0` using `(differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy`. Use `⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩` and prove the remaining obligations. Use `show segre (lift i0 k0 (h y)) = h y`.

Rewrite using `[← hs0]`. Conclude with `(cone_lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2`. Establish `hne' : segre z i0 ≠ 0` using `hs ▸ hne`. Take `⟨h1, h2⟩` from `cone_lift_spec hP i0 k0 hz hne'`. Use `⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩` and prove the remaining obligations.

Use `show lift i0 k0 (h y') ∈ conePts Q`. Rewrite using `[← hs]`. Conclude with `h1`. Use `show Ψ (segre (lift i0 k0 (h y'))) = _`. Rewrite using `[← hs, h2, hs]`.

Conclude with `hΨ`.
-/
theorem cone_sheetLift {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ)
    (hev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ conePts Q, segre z = h y') ∧
      Ψ (h y') = Fin.cons 1 y') :
    ∃ γ, IsSetSheet (conePts Q) Ψ y (h y) γ := by
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (cone_lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := cone_lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ conePts Q
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzw, hΨ⟩`. Establish `hx : x = fun a => segre z (σ a)`. Use function extensionality and compare the values at `a`. Rewrite using `[hzw]`.

Simplify using the standard rewrite rules. Use `⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `r`. Rewrite using `[chartProjMatrix_mulVec, hΨ]`. Both sides reduce to the same expression.

Introduce and unpack `⟨⟨z, hz, h0, rfl⟩, hA⟩`. Establish `hw : (fun i' => segre z (σ (σ.symm i'))) = segre z`. Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules. Use `⟨z, hz, hw.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw]`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun r => ?_) j` and prove the remaining obligations. Rewrite using `[h0]`. Both sides reduce to the same expression.

Establish `h` using `congrFun hA r`. Rewrite `h` using `[chartProjMatrix_mulVec, hw]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem mem_setFibre_iff {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (x : Fin m → ℂ) :
    (fun i' => x (σ.symm i')) ∈ setFibre S Ψ y ↔
      x ∈ setChartSet S σ Ψ ∧ chartProjMatrix σ Ψ *ᵥ x = y := by
  constructor
  · rintro ⟨z, hz, hzw, hΨ⟩
    have hx : x = fun a => segre z (σ a) := by
      funext a
      rw [hzw]
      simp
    refine ⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩
    funext r
    rw [chartProjMatrix_mulVec, hΨ]
    rfl
  · rintro ⟨⟨z, hz, h0, rfl⟩, hA⟩
    have hw : (fun i' => segre z (σ (σ.symm i'))) = segre z := by
      funext i'
      simp
    refine ⟨z, hz, hw.symm, ?_⟩
    rw [hw]
    funext j
    refine Fin.cases ?_ (fun r => ?_) j
    · rw [h0]
      rfl
    · have h := congrFun hA r
      rw [chartProjMatrix_mulVec, hw] at h
      rw [h]
      rfl

/- English proof (translation)
Establish `hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q` using `hQ.2.1.2.1`. Use `set σ := (Fintype.equivFin ((k : K) → ι k)).symm`. Take `⟨hZ, hJ⟩` from `cxChartModel hQ σ Ψ hΨ`. Use `set I := setChartIdeal (conePts Q) σ Ψ`. Use `set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset`.

Use `set A := chartProjMatrix σ Ψ`. Establish `hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes` using `fun J => Set.Finite.mem_toFinset _`. Establish `hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ setChartSet (conePts Q) σ Ψ`. Introduce `x`. Rewrite using `[← hZ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨J, hJF, hx⟩ q hq`. Conclude with `hx q (((hF J).1 hJF).1.2 hq)`. Introduce `hx`. Establish `hle : I ≤ RingHom.ker (MvPolynomial.eval x)` using `fun q hq => RingHom.mem_ker.2 (hx q hq)`.

Establish `: (RingHom.ker (MvPolynomial.eval x)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨J, hJm, hJle⟩` from `Ideal.exists_minimalPrimes_le hle`. Conclude with `⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩`. Take `⟨hle, Δ, hΔ, hgen⟩` from `ComponentsGenericCount.proof _ e F A (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩) (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))`. Establish `hfib : ∀ y, setFibre (conePts Q) Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) '' {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}`.

Introduce `y`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w`.

Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules. Rewrite `hw` using `[← hw']`. Take `⟨hxS, hxA⟩` from `(mem_setFibre_iff σ Ψ y (fun a => w (σ a))).1 hw`. Conclude with `⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩`.

Introduce and unpack `⟨x, ⟨hxU, hxA⟩, rfl⟩`. Conclude with `(mem_setFibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩`. Establish `hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i'))`. Introduce `x x' h`. Use function extensionality and compare the values at `a`.

Simplify using `using congrFun h (σ a)`. Establish `henc : ∀ y, (setFibre (conePts Q) Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard` using `fun y => by rw [hfib y, hinj.injOn.encard_image]`. Use `⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩` and prove the remaining obligations. Use `measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Take `⟨hcount, hsec⟩` from `hgen y h0`. Use `hy ⟨(henc y).trans hcount, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[hfib y]`. Take `⟨x, ⟨hxU, hxA⟩, rfl⟩` from `hw`. Take `⟨U, g, hUo, hyU, hg, hgy, hgU⟩` from `hsec x hxU hxA`.

Rewrite using `[← hgy]`. Use `cone_sheetLift hR Ψ y (fun y' i' => g y' (σ.symm i')) ?_` and prove the remaining obligations. Use `filter_upwards [hUo.mem_nhds hyU] with y' hy'`. Take `⟨hAg, J, hJF, hgJ⟩` from `hgU y' hy'`. Take `⟨z, hz, hzw, hΨz⟩` from `(mem_setFibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩`.

Establish `hgd : DifferentiableAt ℂ g y'` using `hg.differentiableAt (hUo.mem_nhds hy')`. Conclude with `⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩`.
-/
theorem cxGenericCount {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : IsCxVar Q e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsSetGoodProj (conePts Q) Ψ) :
    ∃ d : ℕ, (∀ y, (setFibre (conePts Q) Ψ y).encard ≤ d) ∧
      volume {y : Fin e → ℂ | ¬ ((setFibre (conePts Q) Ψ y).encard = d ∧
        ∀ w ∈ setFibre (conePts Q) Ψ y, ∃ γ, IsSetSheet (conePts Q) Ψ y w γ)} = 0 := by
  classical
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  set σ := (Fintype.equivFin ((k : K) → ι k)).symm
  obtain ⟨hZ, hJ⟩ := cxChartModel hQ σ Ψ hΨ
  set I := setChartIdeal (conePts Q) σ Ψ
  set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset
  set A := chartProjMatrix σ Ψ
  have hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes := fun J => Set.Finite.mem_toFinset _

  have hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ setChartSet (conePts Q) σ Ψ := by
    intro x
    rw [← hZ]
    constructor
    · rintro ⟨J, hJF, hx⟩ q hq
      exact hx q (((hF J).1 hJF).1.2 hq)
    · intro hx
      have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => RingHom.mem_ker.2 (hx q hq)
      have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨J, hJm, hJle⟩ := Ideal.exists_minimalPrimes_le hle
      exact ⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩
  obtain ⟨hle, Δ, hΔ, hgen⟩ := ComponentsGenericCount.proof _ e F A
    (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩)
    (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))

  have hfib : ∀ y, setFibre (conePts Q) Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) ''
      {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} := by
    intro y
    ext w
    constructor
    · intro hw
      have hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w := by
        funext i'
        simp
      rw [← hw'] at hw
      obtain ⟨hxS, hxA⟩ := (mem_setFibre_iff σ Ψ y (fun a => w (σ a))).1 hw
      exact ⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact (mem_setFibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩
  have hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) := by
    intro x x' h
    funext a
    simpa using congrFun h (σ a)
  have henc : ∀ y, (setFibre (conePts Q) Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard :=
    fun y => by rw [hfib y, hinj.injOn.encard_image]
  refine ⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩
  refine measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)
  by_contra h0
  obtain ⟨hcount, hsec⟩ := hgen y h0
  refine hy ⟨(henc y).trans hcount, fun w hw => ?_⟩
  rw [hfib y] at hw
  obtain ⟨x, ⟨hxU, hxA⟩, rfl⟩ := hw
  obtain ⟨U, g, hUo, hyU, hg, hgy, hgU⟩ := hsec x hxU hxA
  rw [← hgy]
  refine cone_sheetLift hR Ψ y (fun y' i' => g y' (σ.symm i')) ?_
  filter_upwards [hUo.mem_nhds hyU] with y' hy'
  obtain ⟨hAg, J, hJF, hgJ⟩ := hgU y' hy'
  obtain ⟨z, hz, hzw, hΨz⟩ := (mem_setFibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩
  have hgd : DifferentiableAt ℂ g y' := hg.differentiableAt (hUo.mem_nhds hy')
  exact ⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩

/- English proof (translation)
Establish `hF : (setFibre S Ψ y).Finite` using `Set.finite_of_encard_eq_coe hy`. Use `choose! γ hγ using hsh`. Take `⟨U, hU, hdisj⟩` from `hF.t2_separation`. Establish `hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ setFibre S Ψ y, (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a`. Use `(hF.eventually_all).2 fun a ha => ?_` and prove the remaining obligations.

Establish `hc` using `(segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt`. Establish `hmem : U a ∈ 𝓝 (segre (γ a y))`. Rewrite using `[(hγ a ha).1]`. Conclude with `(hU a).2.mem_nhds (hU a).1`. Use `filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2`.

Conclude with `⟨⟨h1.2.1, h1.2.2⟩, h2⟩`. Establish `hfib : ∀ y', (∀ a ∈ setFibre S Ψ y, (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a) → setFibre S Ψ y' = (fun a => segre (γ a y')) '' setFibre S Ψ y`. Introduce `y' h`. Establish `hinj : Set.InjOn (fun a => segre (γ a y')) (setFibre S Ψ y)`. Introduce `a ha b hb hab`.

Assume the negation of the conclusion as `hne`. Conclude with `Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)`. Establish `hsub : (fun a => segre (γ a y')) '' setFibre S Ψ y ⊆ setFibre S Ψ y'`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩`.

Use `((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm` and prove the remaining obligations. Rewrite using `[hinj.encard_image, hy]`. Conclude with `hbd y'`. Use `⟨y, γ w, hγ w hw, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2`.

Rewrite `hq2` using `[hfib q.1 hq.1]`. Take `⟨a, ha, hqa⟩` from `hq2`. Establish `haw : a = w`. Assume the negation of the conclusion as `hne`. Conclude with `Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2`.

Rewrite using `[← hqa, haw]`.
-/
theorem cxSimple_of_count {S : Set ((Σ k, ι k) → ℂ)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (setFibre S Ψ y').encard ≤ d) (hy : (setFibre S Ψ y).encard = d)
    (hsh : ∀ w ∈ setFibre S Ψ y, ∃ γ, IsSetSheet S Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ setFibre S Ψ y) : CxComp.cxSimple S Ψ w := by
  have hF : (setFibre S Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ setFibre S Ψ y,
      (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ setFibre S Ψ y, (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → setFibre S Ψ y' = (fun a => segre (γ a y')) '' setFibre S Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (setFibre S Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' setFibre S Ψ y ⊆ setFibre S Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

end Count

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
