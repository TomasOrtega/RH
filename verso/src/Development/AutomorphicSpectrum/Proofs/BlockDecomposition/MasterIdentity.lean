import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisMG

open MeasureTheory Topology

section SlopeTestRemainingChoices

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/- English proof (translation)
Use `⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `h.2 b c hc`. Conclude with `⟨‖T‖ * M, fun z h1 h2 => (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))⟩`.
-/
theorem leftGood_map {f : ℂ → X} {a : ℝ} (T : X →L[ℂ] Y) (h : LeftGood f a) :
    LeftGood (fun z => T (f z)) a := by
  refine ⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩
  obtain ⟨M, hM⟩ := h.2 b c hc
  exact ⟨‖T‖ * M, fun z h1 h2 =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.mono fun _ hz => lt_of_lt_of_le hz hab, fun b' c hc => h.2 b' c (lt_of_lt_of_le hc hab)⟩`.
-/
theorem leftGood_mono {f : ℂ → X} {a b : ℝ} (hab : b ≤ a) (h : LeftGood f a) : LeftGood f b :=
  ⟨h.1.mono fun _ hz => lt_of_lt_of_le hz hab, fun b' c hc => h.2 b' c (lt_of_lt_of_le hc hab)⟩

end SlopeTestRemainingChoices

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/- English proof (translation)
Unfold `eis`. Rewrite using `[← tsum_const_smul'']`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_comm]`.
-/
theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G)
    (t : ℂ) (w : W) : eis Γ K P c ρ Λ g (t • w) = t • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [map_smul, smul_comm]

end Eis

/- English proof (translation)
Introduce `hM hD hH hB`. Introduce `G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar hProb Γ P P' c η η' β L J R N Φ a ζ hpar hLe hR hcR hcL hΦ ha haN hζ hLaw hEqR hEqL`. Take `⟨pr, hpr⟩ : (secSp K P' c ρ).ClosedComplemented` from `Submodule.ClosedComplemented.of_finiteDimensional _`. Set `T : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] secSp K P' c ρ)` to `((ContinuousLinearMap.compL ℂ L W _).flip J).comp (ContinuousLinearMap.compL ℂ W W _ pr)`. Set `TJ : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] W)` to `(ContinuousLinearMap.compL ℂ L W W).flip J`.

Take `⟨hHd, hHc, hHb⟩` from `hH G W K ρ hK hρ μ hHaar hProb Φ hΦ`. Take `⟨hB1, hB2⟩` from `hB G W K ρ hK hρ μ hHaar hProb ζ hζ`. Take `⟨-, hD2⟩` from `hD a N ha`. Establish `hop : LeftGood (fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) (-R)`. Establish `h2` using `leftGood_map T hB2`.

Establish `e : (fun z : ℂ => T (z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) = fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))`. Use function extensionality and compare the values at `fun z => map_smul T z _`. Rewrite `h2` using `[e]`. Conclude with `leftGood_mono (by linarith) h2`. Use `⟨fun z => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)), fun z g => TJ ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)), ?_, fun _ _ _ => rfl, fun z => T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)), leftGood_map T hB1, fun _ _ => rfl⟩` and prove the remaining obligations.

Use `{ le := hLe, pos := hR, convR := hcR, convL := hcL, dEnt := hD2, dNe := ?_, op := hop hol := fun g => TJ.differentiable.comp (hHd g) cont := TJ.continuous.comp hHc bdd := ?_, eqR := ?_, eqL := ?_ }` and prove the remaining obligations. Take `⟨z, hz, haz⟩` from `haN`. Conclude with `⟨z, mul_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero (Complex.exp_ne_zero _) haz)⟩`. Introduce `b a' g`. Take `⟨U, hU, M, hMb⟩` from `hHb b a' g`.

Conclude with `⟨U, hU, ‖TJ‖ * M, fun z h1 h2 g' hg' => (TJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMb z h1 h2 g' hg') (norm_nonneg _))⟩`. Introduce `z hz g w`. Establish `h` using `hEqR z hz g w`. Express the relevant statement in the definitionally equal form `(Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = _`. Rewrite using `[mul_smul, h, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `z hz g w`. Establish `hz' : z.re < 1 / 2` using `by linarith`. Establish `hcont : Continuous (ζ z)`.

Establish `h1 : Continuous fun t : K => (z, t)` using `by fun_prop`. Conclude with `hζ.cont.comp_continuous h1 fun t => ⟨hz', Set.mem_univ _⟩`. Establish `hmem : avg μ ρ (ζ z) (J w) ∈ secSp K P' c ρ` using `hM G W K ρ hK hρ μ hHaar hProb Γ P' c hpar (ζ z) hcont (hLaw z) (J w)`. Establish `hOp : (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W) = (z * (Complex.exp (z ^ 2) * (z - 1))) • avg μ ρ (ζ z) (J w)`. Establish `hp : ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)` using `congrArg Subtype.val (hpr ⟨_, (secSp K P' c ρ).smul_mem (Complex.exp (z ^ 2) * (z - 1)) hmem⟩)`.

Express the relevant statement in the definitionally equal form `z • ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = _`. Rewrite using `[hp, mul_smul z]`. Express the relevant statement in the definitionally equal form `(Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = eis Γ K P' c ρ (fun x => β x - z * η' x) g (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W)`. Rewrite using `[hOp, eis_smul, hEqL z hz g (J w), smul_smul, mul_comm z]`.
-/
theorem master : AvgMem → DGood → HGood → BGood → Master := by
  intro hM hD hH hB
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar hProb Γ P P' c η η' β L J R N Φ a ζ hpar hLe hR
    hcR hcL hΦ ha haN hζ hLaw hEqR hEqL
  obtain ⟨pr, hpr⟩ : (secSp K P' c ρ).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  let T : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] secSp K P' c ρ) :=
    ((ContinuousLinearMap.compL ℂ L W _).flip J).comp (ContinuousLinearMap.compL ℂ W W _ pr)
  let TJ : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] W) := (ContinuousLinearMap.compL ℂ L W W).flip J
  obtain ⟨hHd, hHc, hHb⟩ := hH G W K ρ hK hρ μ hHaar hProb Φ hΦ
  obtain ⟨hB1, hB2⟩ := hB G W K ρ hK hρ μ hHaar hProb ζ hζ
  obtain ⟨-, hD2⟩ := hD a N ha
  have hop : LeftGood (fun z : ℂ =>
      z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) (-R) := by
    have h2 := leftGood_map T hB2
    have e : (fun z : ℂ => T (z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) =
        fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) :=
      funext fun z => map_smul T z _
    rw [e] at h2
    exact leftGood_mono (by linarith) h2
  refine ⟨fun z => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    fun z g => TJ ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)), ?_,
    fun _ _ _ => rfl, fun z => T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    leftGood_map T hB1, fun _ _ => rfl⟩
  refine
    { le := hLe, pos := hR, convR := hcR, convL := hcL, dEnt := hD2, dNe := ?_, op := hop
      hol := fun g => TJ.differentiable.comp (hHd g)
      cont := TJ.continuous.comp hHc
      bdd := ?_, eqR := ?_, eqL := ?_ }
  · obtain ⟨z, hz, haz⟩ := haN
    exact ⟨z, mul_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero (Complex.exp_ne_zero _) haz)⟩
  · intro b a' g
    obtain ⟨U, hU, M, hMb⟩ := hHb b a' g
    exact ⟨U, hU, ‖TJ‖ * M, fun z h1 h2 g' hg' =>
      (TJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMb z h1 h2 g' hg') (norm_nonneg _))⟩
  · intro z hz g w
    have h := hEqR z hz g w
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = _
    rw [mul_smul, h, smul_smul]
    congr 1
    ring
  · intro z hz g w
    have hz' : z.re < 1 / 2 := by linarith
    have hcont : Continuous (ζ z) := by
      have h1 : Continuous fun t : K => (z, t) := by fun_prop
      exact hζ.cont.comp_continuous h1 fun t => ⟨hz', Set.mem_univ _⟩
    have hmem : avg μ ρ (ζ z) (J w) ∈ secSp K P' c ρ :=
      hM G W K ρ hK hρ μ hHaar hProb Γ P' c hpar (ζ z) hcont (hLaw z) (J w)
    have hOp : (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W) =
        (z * (Complex.exp (z ^ 2) * (z - 1))) • avg μ ρ (ζ z) (J w) := by
      have hp : ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) =
          (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w) :=
        congrArg Subtype.val
          (hpr ⟨_, (secSp K P' c ρ).smul_mem (Complex.exp (z ^ 2) * (z - 1)) hmem⟩)
      change z • ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = _
      rw [hp, mul_smul z]
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      eis Γ K P' c ρ (fun x => β x - z * η' x) g
        (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W)
    rw [hOp, eis_smul, hEqL z hz g (J w), smul_smul, mul_comm z]

end GlobalTheory.CompanionTheory.RgEisMG
