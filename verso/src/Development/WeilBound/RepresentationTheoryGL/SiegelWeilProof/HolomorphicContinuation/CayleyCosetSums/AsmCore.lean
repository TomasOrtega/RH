import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IteratedDerivEqOfEventuallyEq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ExpLie : Prop := ∀ (n : ℕ) (x Z : M2 n) (t : ℝ), InG x →
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))

/- English proof (translation)
Establish `h : IsUnit (mR y) ∧ InG (mR y)` using `⟨y.1.isUnit, y.2⟩`. Unfold `lift`. Rewrite using `[dif_pos h]`. Use `congr 1`. Use extensionality with `: 2`.

Both sides reduce to the same expression.
-/
theorem lift_mR' (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  unfold lift
  rw [dif_pos h]
  congr 1
  ext : 2
  rfl

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)`.
-/
theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x :=
  (Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

/- English proof (translation)
Unfold `rC`. Rewrite using `[deriv_const_mul_field', deriv_const_mul_field']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rC_const_mul (Z : M2 n) (a : ℂ) (F : M2 n → ℂ) (x : M2 n) :
    rC Z (fun x => a * F x) x = a * rC Z F x := by
  unfold rC
  rw [deriv_const_mul_field', deriv_const_mul_field']
  ring

/- English proof (translation)
Unfold `rC`. Simplify using the standard rewrite rules.
-/
theorem rC_zero (Z : M2 n) (x : M2 n) : rC Z (fun _ => (0 : ℂ)) x = 0 := by
  unfold rC
  simp

def Van (j : ℕ) (h : ℂ → ℂ) (s : ℂ) : Prop := ∀ k ≤ j, iteratedDeriv k h s = 0

/- English proof (translation)
Introduce `k hk`. Rewrite using `[leib hU k q h hq hh s hs]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hv (k - i) (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem van_mul {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : Van j h s) : Van j (fun z => q z * h z) s := by
  intro k hk
  rw [leib hU k q h hq hh s hs]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hv (k - i) (by omega)]
  simp

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro k _`. Simplify using the standard rewrite rules. Consider the case `insert a S ha ih`. Introduce `k hk`.

Establish `e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z)`. Use function extensionality and compare the values at `z`. Simplify using `[Finset.sum_insert ha]`. Establish `hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U`. Conclude with `DifferentiableOn.fun_sum (fun l _ => hd l)`.

Rewrite using `[e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top) ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]`.
-/
theorem van_sum {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {ι : Type} (S : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ l, DifferentiableOn ℂ (h l) U) {j : ℕ} (hv : ∀ l, Van j (h l) s) : Van j (fun z => ∑ l ∈ S, h l z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => intro k _; simp
  | insert a S ha ih =>
    intro k hk
    have e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z) := by
      funext z; simp [Finset.sum_insert ha]
    have hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U := by
      exact DifferentiableOn.fun_sum (fun l _ => hd l)
    rw [e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top)
      ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]

/- English proof (translation)
Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[leib hU j q h hq hh s hs, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `b hbm hb`. Use `Finset.mem_range.1 hbm` as an intermediate fact.

Rewrite using `[hv (j - b) (by omega)]`. Simplify using the standard rewrite rules. Introduce `h0`. Conclude with `absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0`. Rewrite using `[leib hU i q h hq hh s hs]`.

Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Establish `: b < i + 1` using `Finset.mem_range.1 hb`. Rewrite using `[hv (i - b) (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem iter_mul_low {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : ∀ i < j, iteratedDeriv i h s = 0) :
    iteratedDeriv j (fun z => q z * h z) s = q s * iteratedDeriv j h s ∧
      ∀ i < j, iteratedDeriv i (fun z => q z * h z) s = 0 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [leib hU j q h hq hh s hs, Finset.sum_eq_single 0]
    · simp
    · intro b hbm hb
      have := Finset.mem_range.1 hbm
      rw [hv (j - b) (by omega)]
      simp
    · intro h0; exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
  · rw [leib hU i q h hq hh s hs]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b < i + 1 := Finset.mem_range.1 hb
    rw [hv (i - b) (by omega)]
    simp

/- English proof (translation)
Introduce `hLT hSec hCR`. Introduce `m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g`. Establish `hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t` using `⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩`. Use `haveI : CompactSpace (KR n) := kRCpt n`. Use `letI : MeasurableSpace (KR n) := borel _`.

Use `haveI : BorelSpace (KR n) := ⟨rfl⟩`. Set `μ : Measure (KR n)` to `Measure.haarMeasure ⊤`. Use `haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _`. Use `haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩`. Take `⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩` from `hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g`.

Use `set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ`. Use `set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ`. Establish `hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0`. Introduce `y`. Establish `hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y)` using `by filter_upwards [hU.mem_nhds hs0] with z hz`.

Conclude with `hΦG z hz y`. Establish `hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0` using `fun i hi => hlow i hi (g * ι y)`. Take `⟨h1, h2⟩` from `iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Simplify using `only [hΨ]`.

Rewrite using `[iteratedDeriv_eq_of_eventuallyEq hev j, h1]`. Simplify using `only [hΨ]`. Rewrite using `[iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]`. Establish `hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0`. Introduce `i hi x' hx'`.

Use `(hΨG (toGR x' hx')).2 i hi` as an intermediate fact. Rewrite `this` using `[mR_toGR]`. Then use the resulting hypothesis. Establish `hιKc : Continuous (ιK n)`. Unfold `ιK`. Conclude with `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`.

Establish `hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨⟨toGR x hx.1, hx⟩, rfl⟩`.

Introduce and unpack `⟨k, rfl⟩`. Conclude with `k.2`. Take `⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩` from `hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0`. Take `⟨-, hK⟩` from `hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀`. Use `hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `y`. Simplify using `only [(hΨG y).1]`. Clear the denominators using the available nonvanishing facts. Introduce `y k hk`. Establish `hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k` using `by filter_upwards [hU.mem_nhds hs0] with z hz`.

Conclude with `hK z hz g y k hk`. Simplify using `only [hφ]`. Rewrite using `[iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]`. Introduce `y Q`. Rewrite using `[rC_const_mul]`.

It suffices to establish `h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]`. Take `⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩` from `hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q`. Take `⟨⟨t', hfarId⟩, -⟩` from `hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid`. Use `set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL`. Use `set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef`.

Use `set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef`. Establish `hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ = tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y)` using `fun l => hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y`. Establish `hDs : Differentiable ℂ fun z => D (z - s₀)` using `hDd.comp (differentiable_id.sub_const s₀)`. Establish `hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀)` using `fun l => (hMd l).comp (differentiable_id.sub_const s₀)`. Establish `hLd : DifferentiableOn ℂ L U` using `(hΦrC Q y).1`.

Establish `hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U` using `DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1`. Establish `hRd : DifferentiableOn ℂ R U` using `hcd.mul hsumd`. Establish `hEq : EqOn (fun z => D (z - s₀) * L z) R U`. Take `⟨σ, hσ⟩` from `hRU.1`. Use `set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁`.

Establish `hz₁U : z₁ ∈ U` using `hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))`. Use `(hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_` and prove the remaining obligations. Establish `hopen : IsOpen {z : ℂ | max t' σ < z.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz`. Establish `hzt : t' < z.re` using `lt_of_le_of_lt (le_max_left _ _) hz`.

Establish `hzU : z ∈ U` using `hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))`. Establish `hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y)`. Use `hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2)` and prove the remaining obligations. Establish `e1` using `hΦG z hzU (toGR x' hx')`. Rewrite `e1` using `[mR_toGR]`.

Establish `e2` using `lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')`. Rewrite `e2` using `[mR_toGR]`. Simplify using `only [resG]`. Rewrite using `[e1, e2]`. Use `show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z`.

Rewrite using `[hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]`. Establish `hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R` using `by filter_upwards [hU.mem_nhds hs0] with z hz`. Conclude with `hEq hz`. Establish `hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0`. Introduce `i hi`.

Rewrite using `[(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx') (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]`. Take `⟨hL1, -⟩` from `iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow`. Establish `hnb : ∀ t, InG (nU (herm t) : M2 n)` using `fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq`. Establish `hRv : Van j R s₀`. Apply `van_mul hU hs0 hcd hsumd` to reduce the goal to its premises.

Apply `van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z) (fun l => (hMs l).differentiableOn.mul (hTH l).1)` to reduce the goal to its premises. Introduce `l`. Apply `van_mul hU hs0 (hMs l).differentiableOn (hTH l).1` to reduce the goal to its premises. Introduce `k hk`. Rewrite using `[(hTH l).2 k]`.

Break down `lt_or_eq_of_le hk with hk' | hkj` into its components or cases. Establish `hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0`. Use function extensionality and compare the values at `x`. Unfold `resG lift`. Apply the tactic sequence `split_ifs <;> simp [hlow k hk']`.

Rewrite using `[hz0]`. Simplify using `[tOp]`. Substitute `hkj` using the available equality. Establish `hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0`. Introduce `k'`.

Set `nb : (Fin n → Fin n → ℝ) → GR n` to `fun t => toGR (nU (herm t)) (hnb t)`. Establish `key` using `hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1) (toGR (b l) (hab l).2)`. Use `(integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key` and prove the remaining obligations. Use `show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _`. Simplify using `only [resG]`.

Rewrite using `[lift_mR']`. Unfold `tOp`. Repeatedly rewrite using `[hin, mul_zero, integral_zero]`. Establish `hRj` using `hRv j le_rfl`. Establish `h0 : D 0 * iteratedDeriv j L s₀ = 0`.

Establish `h1` using `iteratedDeriv_eq_of_eventuallyEq hev j`. Rewrite `h1` using `[hL1, hRj, sub_self]`. Conclude with `h1`. Establish `hLj : iteratedDeriv j L s₀ = 0` using `(mul_eq_zero.1 h0).resolve_left hD0`. Rewrite `hLj` using `[(hΦrC Q y).2 j]`.

Conclude with `hLj`.
-/
theorem asmH_of (hF : FarId) (hS : SmoothX) (hT : TopHol) (hR : RcCongr) (hE : ExpLie) : AsmH := by
  intro hLT hSec hCR
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g
  have hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t := ⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩
  haveI : CompactSpace (KR n) := kRCpt n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩

  obtain ⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩ := hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g
  set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ
  set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ

  have hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0 := by
    intro y
    have hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y) := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hΦG z hz y
    have hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0 := fun i hi => hlow i hi (g * ι y)
    obtain ⟨h1, h2⟩ := iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev j, h1]
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]
  have hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0 := by
    intro i hi x' hx'
    have := (hΨG (toGR x' hx')).2 i hi
    rwa [mR_toGR] at this

  have hιKc : Continuous (ιK n) := by
    unfold ιK
    exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨toGR x hx.1, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2

  obtain ⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0
  obtain ⟨-, hK⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀
  refine hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_
  · intro y
    simp only [(hΨG y).1]
    field_simp
  · intro y k hk
    have hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hK z hz g y k hk
    simp only [hφ]
    rw [iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]
  · intro y Q
    rw [rC_const_mul]
    suffices h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]
    obtain ⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q
    obtain ⟨⟨t', hfarId⟩, -⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid
    set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL
    set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef
    set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef
    have hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ =
        tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y) := fun l =>
      hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y
    have hDs : Differentiable ℂ fun z => D (z - s₀) := hDd.comp (differentiable_id.sub_const s₀)
    have hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀) := fun l => (hMd l).comp (differentiable_id.sub_const s₀)
    have hLd : DifferentiableOn ℂ L U := (hΦrC Q y).1
    have hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U :=
      DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1
    have hRd : DifferentiableOn ℂ R U := hcd.mul hsumd

    have hEq : EqOn (fun z => D (z - s₀) * L z) R U := by
      obtain ⟨σ, hσ⟩ := hRU.1
      set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁
      have hz₁U : z₁ ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))
      refine (hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq
        (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_
      have hopen : IsOpen {z : ℂ | max t' σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz
      have hzt : t' < z.re := lt_of_le_of_lt (le_max_left _ _) hz
      have hzU : z ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))
      have hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y) := by
        refine hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1)
          (fun s => (hE n (mR y) (lowQ Q) s y.2).2)
        have e1 := hΦG z hzU (toGR x' hx')
        rw [mR_toGR] at e1
        have e2 := lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')
        rw [mR_toGR] at e2
        simp only [resG]
        rw [e1, e2]
      show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z
      rw [hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]
    have hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hEq hz
    have hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0 := by
      intro i hi
      rw [(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx')
        (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]
    obtain ⟨hL1, -⟩ := iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow
    have hnb : ∀ t, InG (nU (herm t) : M2 n) := fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq
    have hRv : Van j R s₀ := by
      apply van_mul hU hs0 hcd hsumd
      apply van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z)
        (fun l => (hMs l).differentiableOn.mul (hTH l).1)
      intro l
      apply van_mul hU hs0 (hMs l).differentiableOn (hTH l).1
      intro k hk
      rw [(hTH l).2 k]
      rcases lt_or_eq_of_le hk with hk' | hkj
      · have hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0 := by
          funext x
          unfold resG lift
          split_ifs <;> simp [hlow k hk']
        rw [hz0]
        simp [tOp]
      · subst hkj
        have hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
            (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0 := by
          intro k'
          let nb : (Fin n → Fin n → ℝ) → GR n := fun t => toGR (nU (herm t)) (hnb t)
          have key := hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1)
            (toGR (b l) (hab l).2)
          refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key
          show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
              (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _
          simp only [resG]
          rw [lift_mR']
        unfold tOp
        simp_rw [hin, mul_zero, integral_zero]
    have hRj := hRv j le_rfl
    have h0 : D 0 * iteratedDeriv j L s₀ = 0 := by
      have h1 := iteratedDeriv_eq_of_eventuallyEq hev j
      rw [hL1, hRj, sub_self] at h1
      exact h1
    have hLj : iteratedDeriv j L s₀ = 0 := (mul_eq_zero.1 h0).resolve_left hD0
    rw [(hΦrC Q y).2 j] at hLj
    exact hLj

end PositivityTheory.Rg.Sw.HSt
