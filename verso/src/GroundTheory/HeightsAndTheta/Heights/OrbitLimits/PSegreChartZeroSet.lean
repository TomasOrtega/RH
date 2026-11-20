import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace SegreChartZeroSet

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `key : ∀ s : Finset K, (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hz`. Consider the case `insert k s hk ih`.

Establish `h` using `scaleBlock_mem_zeroLocus P hP k (hc k) ih`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `only [scaleBlock, Finset.mem_insert]`. Distinguish the cases in `hpk : p.1 = k`.

Substitute `hpk` using the available equality. Simplify using `[hk]`. Simplify using `[hpk]`. Simplify using `using key Finset.univ`.
-/
theorem scaleAll_mem (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by
  have key : ∀ s : Finset K,
      (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert k s hk ih =>
      have h := scaleBlock_mem_zeroLocus P hP k (hc k) ih
      convert h using 1
      funext p
      simp only [scaleBlock, Finset.mem_insert]
      by_cases hpk : p.1 = k
      · subst hpk
        simp [hk]
      · simp [hpk]
  simpa using key Finset.univ

def liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (f : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  eval₂ (algebraMap ℤ (MvPolynomial (Fin m) ℂ)) (fun p => X (σ.symm (Function.update i p.1 p.2))) f

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[liftPoly, hom_eval₂, eval_map]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Use function extensionality and compare the values at `p`. Simplify using `[chartLift]`.
-/
theorem eval_liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by
  rw [liftPoly, hom_eval₂, eval_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp [chartLift]

end Lemmas

/- English proof (translation)
Introduce `K _ ι _ P m σ i hP`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0` using `fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)`. Establish `ha : x (σ.symm i) = 1`.

Establish `h` using `hv (X (σ.symm i) - 1) (by`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Simplify using `[hzi])`. Rewrite `h` using `[map_sub, eval_X, map_one]`. Conclude with `sub_eq_zero.1 h`.

Establish `hb : ∀ i' : (k : K) → ι k, x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k)))`. Introduce `i'`. Establish `h` using `hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Establish `hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i'`.

Establish `h1` using `congrFun (segre_chartLift σ i z hzi) i'`. Simplify `h1` using `[segre, chartLift]`. Rewrite using `[map_sub, eval_X, map_prod]`. Simplify using `only [eval_X, Equiv.apply_symm_apply]`. Rewrite using `[hs, sub_self])`.

Rewrite `h` using `[map_sub, eval_X, map_prod]`. Simplify using `only [eval_X] at h`. Conclude with `sub_eq_zero.1 h`. Establish `hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0`. Introduce `f hf`.

Rewrite using `[← eval_liftPoly]`. Use `hv _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, hzi, rfl⟩`. Rewrite using `[eval_liftPoly]`. Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0` using `fun k h0 => by`.

Establish `h1 : segre z i = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`. Rewrite `h1` using `[hzi]`. Conclude with `one_ne_zero h1`. Establish `hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p`. Use function extensionality and compare the values at `⟨k, j⟩`.

Rewrite using `[chartLift_segre_apply σ i z hzi, mul_comm]`. Rewrite using `[hcl]`. Conclude with `(scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf`. Use `⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1`.

Simplify using `[chartLift, ha]`. Use function extensionality and compare the values at `a show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩`. Simplify using `only [chartLift]`. Rewrite using `[← hb, Equiv.symm_apply_apply]`. Introduce `x hx q hq`.

Rewrite `hq` using `[segreChartIdeal, mem_vanishingIdeal_iff]`. Conclude with `hq x hx`.
-/
theorem proof : Statement := by
  intro K _ ι _ P m σ i hP
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0 :=
      fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)
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
          simpa [segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      rw [← eval_liftPoly]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPoly]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

end SegreChartZeroSet

end GroundTheory.Heights₂.Heights
