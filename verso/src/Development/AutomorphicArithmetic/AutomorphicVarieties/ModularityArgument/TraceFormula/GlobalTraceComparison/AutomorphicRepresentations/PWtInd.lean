import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegrableShift
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor

noncomputable section

open NumberField MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc DiscreteGroups.T1.G
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH borelSpace_H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Take `⟨_, γ, rfl⟩` from `γ`. Conclude with `hf.2.1 γ.1 x`.
-/
private theorem slab_rat {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (γ : ratH E n 0) (x : GA E n) :
    f ((γ : H E n 0).1 * x) = f x := by
  obtain ⟨_, γ, rfl⟩ := γ
  exact hf.2.1 γ.1 x

/- English proof (translation)
Establish `h : (x * aS E n s).1 = splitCentre E n s * x.1` using `(splitCentre_comm _ _).symm`. Rewrite using `[h]`. Conclude with `hf.2.2.1 s x.1`.
-/
private theorem slab_aS {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (x : H E n 0) (s : ℝ) :
    f (x * aS E n s).1 = f x.1 := by
  have h : (x * aS E n s).1 = splitCentre E n s * x.1 := (splitCentre_comm _ _).symm
  rw [h]
  exact hf.2.2.1 s x.1

/- English proof (translation)
The claim follows from `((Complex.continuous_conj.comp (ha.comp continuous_fst)).mul (hb.comp continuous_fst)).mul (hu.comp continuous_ldet)`.
-/
private theorem cont_pair {a b : GA E n → ℂ} (ha : Continuous a) (hb : Continuous b) {u : ℝ → ℂ} (hu : Continuous u) :
    Continuous fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x) :=
  ((Complex.continuous_conj.comp (ha.comp continuous_fst)).mul (hb.comp continuous_fst)).mul
    (hu.comp continuous_ldet)

/- English proof (translation)
Take `⟨χ, h1, -, hχs, -⟩` from `exists_continuous_one_zero_of_isCompact (X := ℝ) hs.isCompact isClosed_empty (Set.disjoint_empty _)`. Establish `hχ : Continuous fun s => ((χ s : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp χ.continuous`. Establish `hχc : HasCompactSupport fun s => ((χ s : ℝ) : ℂ)` using `hχs.comp_left Complex.ofReal_zero`. Establish `hA : MemLp (fun x : H E n 0 => star (a x.1 * ((χ (ldet x) : ℝ) : ℂ))) 2 D.ν` using `(ha.2.2.2 _ hχ hχc).star`. Establish `hB` using `hb.2.2.2 u hu hs`.

Use `(hA.integrable_mul hB).congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : u (ldet x) = 0`. Simplify using `[h0]`. Establish `: χ (ldet x) = 1` using `h1 (subset_tsupport _ h0)`. Simplify using `[this, mul_assoc]`.
-/
private theorem pair_integrable {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) :
    Integrable (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) D.ν := by
  obtain ⟨χ, h1, -, hχs, -⟩ := exists_continuous_one_zero_of_isCompact (X := ℝ) hs.isCompact isClosed_empty
    (Set.disjoint_empty _)
  have hχ : Continuous fun s => ((χ s : ℝ) : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hχc : HasCompactSupport fun s => ((χ s : ℝ) : ℂ) := hχs.comp_left Complex.ofReal_zero
  have hA : MemLp (fun x : H E n 0 => star (a x.1 * ((χ (ldet x) : ℝ) : ℂ))) 2 D.ν := (ha.2.2.2 _ hχ hχc).star
  have hB := hb.2.2.2 u hu hs
  refine (hA.integrable_mul hB).congr (ae_of_all _ fun x => ?_)
  by_cases h0 : u (ldet x) = 0
  · simp [h0]
  · have : χ (ldet x) = 1 := h1 (subset_tsupport _ h0)
    simp [this, mul_assoc]

/- English proof (translation)
Establish `h` using `integral_affine u r c hc`. Establish `h2` using `integral_neg_eq_self (fun s : ℝ => u (r - s * c)) volume`. Establish `e : (fun s : ℝ => u (r - -s * c)) = fun s => u (r + s * c)`. Use function extensionality and compare the values at `s`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e] at h2`. Rewrite using `[h2, h, Complex.real_smul, Complex.ofReal_inv]`.
-/
private theorem integral_u_shift (u : ℝ → ℂ) (r c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, u (r + s * c) = (c : ℂ)⁻¹ * ∫ s, u s := by
  have h := integral_affine u r c hc
  have h2 := integral_neg_eq_self (fun s : ℝ => u (r - s * c)) volume
  have e : (fun s : ℝ => u (r - -s * c)) = fun s => u (r + s * c) := by
    funext s
    congr 1
    ring
  simp only [e] at h2
  rw [h2, h, Complex.real_smul, Complex.ofReal_inv]

/- English proof (translation)
Establish `hc : 0 < ldet (aS E n 1)` using `lg_e_pos hn`. Establish `hinv : ∀ (γ : ratH E n 0) x, (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) ((γ : H E n 0) * x) = (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) x` using `fun γ x => by show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _`. Rewrite using `[slab_rat ha, slab_rat hb, ldet_rat]`. Establish `h` using `(avgInt_holds E n hn D _ hinv (cont_pair ha.1 hb.1 hu) (pair_integrable ha hb hu hs) w hw hws hw1).2`. Establish `hin : ∀ x : H E n 0, w (ldet x) * ∫ s : ℝ, starRingEnd ℂ (a (x * aS E n s).1) * b (x * aS E n s).1 * u (ldet (x * aS E n s)) = ((ldet (aS E n 1) : ℂ)⁻¹ * ∫ s, u s) * (starRingEnd ℂ (a x.1) * b x.1 * w (ldet x))` using `fun x => by`.

Simplify using `only [slab_aS ha, slab_aS hb, ldet_mul_aS]`. Rewrite using `[integral_const_mul, integral_u_shift u _ _ hc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hin] at h`. Rewrite `h` using `[integral_const_mul]`.

Establish `hc' : (ldet (aS E n 1) : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Use `show ∫ x, _ ∂D.ν = (∫ s, u s) * ∫ x, _ ∂D.ν`. Rewrite using `[h, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]`.
-/
private theorem pair_wt (hn : 1 ≤ n) {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u w : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hw : Continuous w) (hws : HasCompactSupport w)
    (hw1 : ∫ s, w s = 1) : prW D u a b = (∫ s, u s) * prW D w a b := by
  have hc : 0 < ldet (aS E n 1) := lg_e_pos hn
  have hinv : ∀ (γ : ratH E n 0) x, (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) ((γ : H E n 0) * x) =
      (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) x := fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]
  have h := (avgInt_holds E n hn D _ hinv (cont_pair ha.1 hb.1 hu) (pair_integrable ha hb hu hs) w hw hws hw1).2
  have hin : ∀ x : H E n 0, w (ldet x) * ∫ s : ℝ, starRingEnd ℂ (a (x * aS E n s).1) * b (x * aS E n s).1 * u (ldet (x * aS E n s)) =
      ((ldet (aS E n 1) : ℂ)⁻¹ * ∫ s, u s) * (starRingEnd ℂ (a x.1) * b x.1 * w (ldet x)) := fun x => by
    simp only [slab_aS ha, slab_aS hb, ldet_mul_aS]
    rw [integral_const_mul, integral_u_shift u _ _ hc]
    ring
  simp only [hin] at h
  rw [integral_const_mul] at h
  have hc' : (ldet (aS E n 1) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  show ∫ x, _ ∂D.ν = (∫ s, u s) * ∫ x, _ ∂D.ν
  rw [h, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]

/- English proof (translation)
Establish `h : ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det` using `Dcy.logAbs_det_mul' x.1 g`. Rewrite using `[h, hg, add_zero]`.
-/
private theorem ldet_shift {g : GA E n} (hg : logAbs g.val.det = 0) (x : H E n 0) :
    ldet (x * ((g, 1) : H E n 0)) = ldet x := by
  have h : ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det := Dcy.logAbs_det_mul' x.1 g
  rw [h, hg, add_zero]

/- English proof (translation)
Establish `hc : Continuous fun x => a (x * g)` using `ha.1.comp (continuous_mul_right g)`. Use `⟨hc, fun γ x => ?_, fun t x => ?_, fun u hu hs => ?_⟩` and prove the remaining obligations. Use `show a (_ * x * g) = a (x * g)`. Rewrite using `[mul_assoc]`. Conclude with `ha.2.1 γ _`.

Use `show a (_ * x * g) = a (x * g)`. Rewrite using `[mul_assoc]`. Conclude with `ha.2.2.1 t _`. Establish `hm` using `ha.2.2.2 u hu hs`. Establish `hcm : Continuous fun x : H E n 0 => a (x.1 * g) * u (ldet x)` using `(hc.comp continuous_fst).mul (hu.comp continuous_ldet)`.

Use `⟨hcm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hsh` using `lintegral_shift D (fun x : H E n 0 => ‖a x.1 * u (ldet x)‖ₑ ^ (2 : ENNReal).toReal) (fun γ x => by show ‖a ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x))‖ₑ ^ _ = _`. Rewrite using `[slab_rat ha, ldet_rat]) ((g, 1) : H E n 0)`. Simplify using `only [ldet_shift hg] at hsh`. Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]`.

Establish `h2` using `hm.2`. Rewrite `h2` using `[eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← hsh]`. Conclude with `h2`.
-/
private theorem slab_rt (D : Dom E n 0) {a : GA E n → ℂ} (ha : Slab D a) {g : GA E n} (hg : logAbs g.val.det = 0) :
    Slab D fun x => a (x * g) := by
  have hc : Continuous fun x => a (x * g) := ha.1.comp (continuous_mul_right g)
  refine ⟨hc, fun γ x => ?_, fun t x => ?_, fun u hu hs => ?_⟩
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.1 γ _
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.2.1 t _
  · have hm := ha.2.2.2 u hu hs
    have hcm : Continuous fun x : H E n 0 => a (x.1 * g) * u (ldet x) :=
      (hc.comp continuous_fst).mul (hu.comp continuous_ldet)
    refine ⟨hcm.aestronglyMeasurable, ?_⟩
    have hsh := lintegral_shift D (fun x : H E n 0 => ‖a x.1 * u (ldet x)‖ₑ ^ (2 : ENNReal).toReal) (fun γ x => by
      show ‖a ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x))‖ₑ ^ _ = _
      rw [slab_rat ha, ldet_rat]) ((g, 1) : H E n 0)
    simp only [ldet_shift hg] at hsh
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    have h2 := hm.2
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← hsh] at h2
    exact h2

/- English proof (translation)
Establish `h` using `integral_shift D (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) (fun γ x => by show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _`. Rewrite using `[slab_rat ha, slab_rat hb, ldet_rat]) ((g, 1) : H E n 0)`. Simplify using `only [ldet_shift hg] at h`. Conclude with `h`.
-/
private theorem pair_rt (D : Dom E n 0) {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) (u : ℝ → ℂ) {g : GA E n}
    (hg : logAbs g.val.det = 0) : prW D u (fun x => a (x * g)) (fun x => b (x * g)) = prW D u a b := by
  have h := integral_shift D (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) (fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]) ((g, 1) : H E n 0)
  simp only [ldet_shift hg] at h
  exact h

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

/- English proof (translation)
Introduce `_ E _ _ _ n hn D a b ha hb u hu hs`. Conclude with `⟨pair_integrable ha hb hu hs, fun w hw hws hw1 => pair_wt hn ha hb hu hs hw hws hw1, fun g hg => ⟨slab_rt D ha hg, pair_rt D ha hb u hg⟩⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtInd_pf :
    Basic → WtInd := by
  intro _ E _ _ _ n hn D a b ha hb u hu hs
  exact ⟨pair_integrable ha hb hu hs, fun w hw hws hw1 => pair_wt hn ha hb hu hs hw hws hw1,
    fun g hg => ⟨slab_rt D ha hg, pair_rt D ha hb u hg⟩⟩

end
