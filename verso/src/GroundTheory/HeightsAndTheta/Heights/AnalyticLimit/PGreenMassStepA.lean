import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC mInt MIntegrable logNormSec)

noncomputable section

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W} {L : LocPot W}
  {s : W → W → ℂ}

/- English proof (translation)
The claim follows from `hs.2 y x y ⟨L.mem_U y, hy⟩`.
-/
theorem secNorm_eq_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hs.2 y x y ⟨L.mem_U y, hy⟩

/- English proof (translation)
Introduce `j`. Use `contDiffOn_of_locally_contDiffOn fun y hy => ?_` and prove the remaining obligations. Use `⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y), (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _), ⟨hy.1, L.mem_U _⟩, ?_⟩` and prove the remaining obligations. Use `set p := (A.chart j).symm y`. Establish `h1 : ContDiffOn ℝ ∞ (fun z => ‖s p ((A.chart j).symm z)‖ ^ 2) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p)` using `contDiff_norm_sq ℝ |>.comp_contDiffOn (((hs.1 p j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ)`.

Establish `h2 : ContDiffOn ℝ ∞ (fun z => Real.exp (-L.φ p ((A.chart j).symm z)) ^ 2) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p)` using `(Real.contDiff_exp.comp_contDiffOn (hL.1 p j).neg).pow 2`. Use `((h1.mul h2).mono fun z hz => hz.2).congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[secNorm_eq_local hs hz.2.2, mul_pow]`.
-/
theorem smooth_secNorm_sq (hL : IsPotential A L) (hs : IsSection A L s) :
    A.Smooth fun x => secNorm L s x ^ 2 := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y),
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _), ⟨hy.1, L.mem_U _⟩, ?_⟩
  set p := (A.chart j).symm y
  have h1 : ContDiffOn ℝ ∞ (fun z => ‖s p ((A.chart j).symm z)‖ ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    contDiff_norm_sq ℝ |>.comp_contDiffOn
      (((hs.1 p j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ)
  have h2 : ContDiffOn ℝ ∞ (fun z => Real.exp (-L.φ p ((A.chart j).symm z)) ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    (Real.contDiff_exp.comp_contDiffOn (hL.1 p j).neg).pow 2
  refine ((h1.mul h2).mono fun z hz => hz.2).congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [secNorm_eq_local hs hz.2.2, mul_pow]

/- English proof (translation)
Introduce `j`. Establish `h1 : ContDiffOn ℝ ∞ (fun z => secNorm L s ((A.chart j).symm z) ^ 2 + ε) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ)` using `(smooth_secNorm_sq hL hs j).add contDiffOn_const`. Conclude with `h1.log fun z _ => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'`.
-/
theorem smooth_log_secNorm_sq_add (hL : IsPotential A L) (hs : IsSection A L s) {ε : ℝ}
    (hε : 0 < ε) : A.Smooth fun x => Real.log (secNorm L s x ^ 2 + ε) := by
  intro j
  have h1 : ContDiffOn ℝ ∞ (fun z => secNorm L s ((A.chart j).symm z) ^ 2 + ε)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) :=
    (smooth_secNorm_sq hL hs j).add contDiffOn_const
  exact h1.log fun z _ => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'

def secZero (L : LocPot W) (s : W → W → ℂ) : Set W := {x | secNorm L s x = 0}

/- English proof (translation)
Use `show secNorm L s y = 0 ↔ _`. Rewrite using `[secNorm_eq_local hs hy, mul_eq_zero, norm_eq_zero]`. Simplify using `[(Real.exp_pos _).ne']`.
-/
theorem mem_secZero_iff_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    y ∈ secZero L s ↔ s x y = 0 := by
  show secNorm L s y = 0 ↔ _
  rw [secNorm_eq_local hs hy, mul_eq_zero, norm_eq_zero]
  simp [(Real.exp_pos _).ne']

/- English proof (translation)
Introduce `x`. Use `⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_sep_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, hy⟩`. Conclude with `⟨hy, fun _ => (mem_secZero_iff_local hs hy).1 h⟩`. Introduce and unpack `⟨hy, h⟩`. Conclude with `⟨(mem_secZero_iff_local hs hy).2 (h 0), hy⟩`.
-/
theorem isAnalyticSubset_secZero (hs : IsSection A L s) : A.IsAnalyticSubset (secZero L s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_sep_iff]
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨hy, fun _ => (mem_secZero_iff_local hs hy).1 h⟩
  · rintro ⟨hy, h⟩
    exact ⟨(mem_secZero_iff_local hs hy).2 (h 0), hy⟩

/- English proof (translation)
Use `Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨U, hUZ, hU, hxU⟩` from `mem_interior.1 hx`. Take `⟨ψ, -, hxψ, hψL, σ, -, -, v, -, hv0, hsx⟩` from `hsnc x`. Establish `hcoord : ∀ y ∈ ψ.source, y ∈ U → ∃ i, ψ y i = 0`. Introduce `y hy hyU`.

Establish `h0 : s x y = 0` using `(mem_secZero_iff_local hs (hψL hy)).1 (hUZ hyU)`. Rewrite `h0` using `[hsx y hy, mul_eq_zero]`. Break down `h0 with h0 | h0` into its components or cases. Conclude with `absurd h0 (hv0 y hy)`. Take `⟨k, -, hk⟩` from `Finset.prod_eq_zero_iff.1 h0`.

Consider the cases of `hσ : σ k with`. Consider the case `none => simp [hσ] at hk`. Consider the case `some i`. Simplify using `only [hσ] at hk`. Conclude with `⟨i, eq_zero_of_pow_eq_zero hk⟩`.

Establish `hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U)` using `ψ.isOpen_inter_preimage_symm hU`. Establish `hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' U` using `⟨ψ.map_source hxψ, by simp [ψ.left_inv hxψ, hxU]⟩`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.1 hO _ hxO`. Set `w : Fin e → ℂ` to `fun i => if ψ x i = 0 then ((δ / 2 : ℝ) : ℂ) else ψ x i`. Establish `hw0 : ∀ i, w i ≠ 0`.

Introduce `i`. Distinguish the cases in `h : ψ x i = 0`. Simplify using `only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [w, if_neg h]`.

Conclude with `h`. Establish `hwb : w ∈ Metric.ball (ψ x) δ`. Rewrite using `[Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hδ]`. Introduce `i`. Distinguish the cases in `h : ψ x i = 0`.

Rewrite using `[Pi.sub_apply]`. Simplify using `only [w]`. Rewrite using `[if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]`.

Conclude with `hδ`. Take `⟨hwt, hwU⟩` from `hball hwb`. Take `⟨i, hi⟩` from `hcoord _ (ψ.map_target hwt) hwU`. Rewrite `hi` using `[ψ.right_inv hwt]`. Conclude with `hw0 i hi`.
-/
theorem interior_secZero {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) : interior (secZero L s) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUZ, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, v, -, hv0, hsx⟩ := hsnc x
  have hcoord : ∀ y ∈ ψ.source, y ∈ U → ∃ i, ψ y i = 0 := by
    intro y hy hyU
    have h0 : s x y = 0 := (mem_secZero_iff_local hs (hψL hy)).1 (hUZ hyU)
    rw [hsx y hy, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (hv0 y hy)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h0
      cases hσ : σ k with
      | none => simp [hσ] at hk
      | some i =>
        simp only [hσ] at hk
        exact ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) := ψ.isOpen_inter_preimage_symm hU
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' U :=
    ⟨ψ.map_source hxψ, by simp [ψ.left_inv hxψ, hxU]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin e → ℂ := fun i => if ψ x i = 0 then ((δ / 2 : ℝ) : ℂ) else ψ x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : ψ x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ Metric.ball (ψ x) δ := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hδ]
    intro i
    by_cases h : ψ x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hδ
  obtain ⟨hwt, hwU⟩ := hball hwb
  obtain ⟨i, hi⟩ := hcoord _ (ψ.map_target hwt) hwU
  rw [ψ.right_inv hwt] at hi
  exact hw0 i hi

def greenSplit (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  (-2) * logNormSec L s x + Real.log (secNorm L s x ^ 2 + ε)

/- English proof (translation)
Establish `hn : secNorm L s x ≠ 0` using `hx`. Establish `hn2 : secNorm L s x ^ 2 ≠ 0` using `pow_ne_zero 2 hn`. Establish `hlog : logNormSec L s x = Real.log (secNorm L s x)` using `rfl`. Unfold `greenEp greenSplit`. Rewrite using `[hlog, one_add_div hn2, Real.log_div (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne' hn2, Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem greenEp_eq_split {ε : ℝ} (hε : 0 < ε) {x : W} (hx : x ∉ secZero L s) :
    greenEp L s ε x = greenSplit L s ε x := by
  have hn : secNorm L s x ≠ 0 := hx
  have hn2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hlog : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp greenSplit
  rw [hlog, one_add_div hn2, Real.log_div (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne' hn2,
    Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Establish `h1` using `ReciprocityTheory.AnForm.M.logNormIntegrable A L s m Δ hL hs hsnc Φ hΦ`. Establish `h2` using `ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hΦ _ (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth A (smooth_log_secNorm_sq_add hL hs hε))`. Introduce `j K hK hc`. Establish `: IntegrableOn (fun y => -2 * (logNormSec L s ((A.chart j).symm y) * ReciprocityTheory.AnForm.M.locDens A Φ j y) + Real.log (secNorm L s ((A.chart j).symm y) ^ 2 + ε) * ReciprocityTheory.AnForm.M.locDens A Φ j y) K` using `((h1 j K hK hc).const_mul (-2)).add (h2 j K hK hc)`. Use `this.congr_fun (fun y _ => ?_) hc.measurableSet` and prove the remaining obligations.

Simplify using `only [greenSplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mIntegrable_greenSplit [CompactSpace W] [T2Space W] {r : ℕ} {m : Fin r → ℕ}
    {Δ : Fin r → Set W} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m Δ)
    {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) (hΦ : ∀ i, IsPotential A (Φ i)) :
    MIntegrable A Φ (greenSplit L s ε) := by
  have h1 := ReciprocityTheory.AnForm.M.logNormIntegrable A L s m Δ hL hs hsnc Φ hΦ
  have h2 := ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hΦ _
    (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth A (smooth_log_secNorm_sq_add hL hs hε))
  intro j K hK hc
  have : IntegrableOn (fun y => -2 * (logNormSec L s ((A.chart j).symm y) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) + Real.log (secNorm L s ((A.chart j).symm y) ^ 2 + ε) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) K :=
    ((h1 j K hK hc).const_mul (-2)).add (h2 j K hK hc)
  refine this.congr_fun (fun y _ => ?_) hc.measurableSet
  simp only [greenSplit]
  ring

/- English proof (translation)
The claim follows from `ReciprocityTheory.AnForm.M.mIntCongrNull A Φ (secZero L s) (isAnalyticSubset_secZero hs) (interior_secZero hs hsnc) _ _ fun _ hx => greenEp_eq_split hε hx`.
-/
theorem mInt_greenEp_eq_split {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) :
    mInt A Φ (greenEp L s ε) = mInt A Φ (greenSplit L s ε) :=
  ReciprocityTheory.AnForm.M.mIntCongrNull A Φ (secZero L s) (isAnalyticSubset_secZero hs)
    (interior_secZero hs hsnc) _ _ fun _ hx => greenEp_eq_split hε hx

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
