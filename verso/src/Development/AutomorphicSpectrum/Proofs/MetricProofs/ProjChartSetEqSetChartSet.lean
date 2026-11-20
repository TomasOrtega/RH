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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def setChartSet (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def setChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setChartSet S σ Ψ)

def setSegChartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def setSegChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setSegChartSet S σ i)

def setSegreCone (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, x = fun a => segre z (σ a)}

/- English proof (translation)
The claim follows from `hQ`.
-/
theorem isMultiHomogIdeal_toR {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal Q) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ

/- English proof (translation)
Use `⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 k`. Conclude with `⟨i, mul_ne_zero (hc k) hi⟩`.
-/
theorem cone_scale {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : (fun p => c p.1 * z p) ∈ conePts Q := by
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

/- English proof (translation)
Take `⟨k0⟩` from `‹Nonempty K›`. Use `⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩` and prove the remaining obligations. Use `split_ifs`. Conclude with `hc`. Conclude with `one_ne_zero`.

Conclude with `GoodChartZeroSet.segre_scaleBlock k0 c z`.
-/
theorem exists_segre_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) {c : ℂ} (hc : c ≠ 0) :
    ∃ z' ∈ conePts Q, segre z' = c • segre z := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩
  · split_ifs
    · exact hc
    · exact one_ne_zero
  · exact GoodChartZeroSet.segre_scaleBlock k0 c z

end Defs

section ZeroSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ)) f

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => simp [liftPolyC]`. Consider the case `add f g hf hg`. Simplify using `only [liftPolyC, map_add] at hf hg ⊢`. Rewrite using `[hf, hg]`.

Consider the case `mul_X f q hf`. Simplify using `only [liftPolyC, map_mul] at hf ⊢`. Rewrite using `[hf]`. Simplify using `[chartLift]`.
-/
theorem eval_liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (f : MRingOver ℂ ι) :
    eval x (liftPolyC σ i f) = eval (chartLift σ i x) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [liftPolyC]
  | add f g hf hg =>
    simp only [liftPolyC, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [liftPolyC, map_mul] at hf ⊢
    rw [hf]
    simp [chartLift]

/- English proof (translation)
Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) → eval x q = 0` using `fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)`. Establish `ha : x (σ.symm i) = 1`. Establish `h` using `hv (X (σ.symm i) - 1) (by`.

Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Simplify using `[hzi])`. Rewrite `h` using `[map_sub, eval_X, map_one]`. Conclude with `sub_eq_zero.1 h`. Establish `hb : ∀ i' : (k : K) → ι k, x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k)))`.

Introduce `i'`. Establish `h` using `hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Establish `hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i'`. Establish `h1` using `congrFun (segre_chartLift σ i z hzi) i'`.

Simplify `h1` using `[ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift]`. Rewrite using `[map_sub, eval_X, map_prod]`. Simplify using `only [eval_X, Equiv.apply_symm_apply]`. Rewrite using `[hs, sub_self])`. Rewrite `h` using `[map_sub, eval_X, map_prod]`.

Simplify using `only [eval_X] at h`. Conclude with `sub_eq_zero.1 h`. Establish `hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0`. Introduce `f hf`. Rewrite using `[← eval_liftPolyC]`.

Use `hv _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, hzi, rfl⟩`. Rewrite using `[eval_liftPolyC]`. Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`. Establish `h1 : segre z i = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`.

Rewrite `h1` using `[hzi]`. Conclude with `one_ne_zero h1`. Establish `hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p`. Use function extensionality and compare the values at `⟨k, j⟩`. Rewrite using `[chartLift_segre_apply σ i z hzi, mul_comm]`.

Rewrite using `[hcl]`. Conclude with `(cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf`. Use `⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1`. Simplify using `[chartLift, ha]`.

Use function extensionality and compare the values at `a show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩`. Simplify using `only [chartLift]`. Rewrite using `[← hb, Equiv.symm_apply_apply]`. Introduce `x hx q hq`. Rewrite `hq` using `[setSegChartIdeal, mem_vanishingIdeal_iff]`.

Conclude with `hq x hx`.
-/
theorem segChart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    zeroSet (setSegChartIdeal (conePts Q) σ i) = setSegChartSet (conePts Q) σ i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) →
        eval x q = 0 :=
      fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0 := by
      intro f hf
      rw [← eval_liftPolyC]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPolyC]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

/- English proof (translation)
Apply `Set.Subset.antisymm` to reduce the goal to its premises. Use `swap`. Introduce `x hx q hq`. Rewrite `hq` using `[setChartIdeal, mem_vanishingIdeal_iff]`. Conclude with `hq x hx`.

Introduce `x hx`. Establish `hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0` using `fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)`. Establish `hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z` using `fun z => by`. Use function extensionality and compare the values at `i'`. Rewrite using `[Equiv.apply_symm_apply]`.

Establish `hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1`. Establish `h` using `hv (GoodChartZeroSet.linForm σ Ψ - 1) (by`. Introduce and unpack `_ ⟨z, -, hz1, rfl⟩`. Rewrite using `[map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])`. Rewrite `h` using `[map_sub, GoodChartZeroSet.eval_linForm, map_one]`.

Conclude with `sub_eq_zero.1 h`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, x a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, ne_eq, not_not] at h`. Establish `h0 : (fun i' => x (σ.symm i')) = 0` using `funext fun i' => h _`.

Rewrite `hx1` using `[h0, map_zero]`. Conclude with `zero_ne_one hx1`. Establish `hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a))`. Introduce `f hf`. Rewrite `hf` using `[setSegChartIdeal, mem_vanishingIdeal_iff]`.

Establish `hg` using `hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1), X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by`. Introduce and unpack `_ ⟨z, hz, -, rfl⟩`. Distinguish the cases in `h0 : segre z (σ a) = 0`. Simplify using `[h0]`. Rewrite using `[GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]`.

Take `⟨z', hz', hz'e⟩` from `exists_segre_smul hQ hz (inv_ne_zero h0)`. Use `mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]`. Use function extensionality and compare the values at `b`. Rewrite using `[hz'e]`.

Use the proof step `rfl)`. Rewrite `hg` using `[GoodChartZeroSet.eval_homogenize f le_rfl a x ha]`. Conclude with `(mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)`. Rewrite `hzero` using `[segChart_zeroSet hQ σ (σ a)]`. Take `⟨z', hz', -, hz'e⟩` from `hzero`.

Take `⟨z, hz, hze⟩` from `exists_segre_smul hQ hz' ha`. Establish `hxz : x = fun b => segre z (σ b)`. Use function extensionality and compare the values at `b`. Establish `hb` using `congrFun hz'e b`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hb`.

Rewrite using `[hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]`. Use `⟨z, hz, ?_, hxz⟩` and prove the remaining obligations. Rewrite using `[← hseg z, ← hx1, hxz]`.
-/
theorem chart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ := by
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [setChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (GoodChartZeroSet.linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, GoodChartZeroSet.eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a)) := by
    intro f hf
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul hQ hz (inv_ne_zero h0)
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [GoodChartZeroSet.eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [segChart_zeroSet hQ σ (σ a)] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul hQ hz' ha
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end ZeroSet

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
