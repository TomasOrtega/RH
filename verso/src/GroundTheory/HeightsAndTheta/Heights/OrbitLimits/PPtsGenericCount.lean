import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSheetLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet)

namespace PtsGenericCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e m : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzw, hΨ⟩`. Establish `hx : x = fun a => segre z (σ a)`. Use function extensionality and compare the values at `a`. Rewrite using `[hzw]`.

Simplify using the standard rewrite rules. Use `⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `r`. Rewrite using `[chartProjMatrix_mulVec, hΨ]`. Both sides reduce to the same expression.

Introduce and unpack `⟨⟨z, hz, h0, rfl⟩, hA⟩`. Establish `hw : (fun i' => segre z (σ (σ.symm i'))) = segre z`. Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules. Use `⟨z, hz, hw.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw]`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun r => ?_) j` and prove the remaining obligations. Rewrite using `[h0]`. Both sides reduce to the same expression.

Establish `h` using `congrFun hA r`. Rewrite `h` using `[chartProjMatrix_mulVec, hw]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem mem_fibre_iff {P : Ideal (MRing ι)} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (x : Fin m → ℂ) :
    (fun i' => x (σ.symm i')) ∈ fibre P Ψ y ↔
      x ∈ projChartSet P σ Ψ ∧ chartProjMatrix σ Ψ *ᵥ x = y := by
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
Introduce `K _ ι _ P e Ψ hP hΨ`. Use `set σ := (Fintype.equivFin ((k : K) → ι k)).symm`. Take `⟨hZ, hJ⟩` from `hA K ι P e _ σ Ψ hP hΨ`. Use `set I := projChartIdeal P σ Ψ`. Use `set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset`.

Use `set A := chartProjMatrix σ Ψ`. Establish `hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes` using `fun J => Set.Finite.mem_toFinset _`. Establish `hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ projChartSet P σ Ψ`. Introduce `x`. Rewrite using `[← hZ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨J, hJF, hx⟩ q hq`. Conclude with `hx q (((hF J).1 hJF).1.2 hq)`. Introduce `hx`. Establish `hle : I ≤ RingHom.ker (MvPolynomial.eval x)` using `fun q hq => RingHom.mem_ker.2 (hx q hq)`.

Establish `: (RingHom.ker (MvPolynomial.eval x)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨J, hJm, hJle⟩` from `Ideal.exists_minimalPrimes_le hle`. Conclude with `⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩`. Take `⟨hle, Δ, hΔ, hgen⟩` from `hB _ e F A (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩) (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))`. Establish `hfib : ∀ y, fibre P Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) '' {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}`.

Introduce `y`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w`.

Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules. Rewrite `hw` using `[← hw']`. Take `⟨hxS, hxA⟩` from `(mem_fibre_iff (P := P) σ Ψ y (fun a => w (σ a))).1 hw`. Conclude with `⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩`.

Introduce and unpack `⟨x, ⟨hxU, hxA⟩, rfl⟩`. Conclude with `(mem_fibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩`. Establish `hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i'))`. Introduce `x x' h`. Use function extensionality and compare the values at `a`.

Simplify using `using congrFun h (σ a)`. Establish `henc : ∀ y, (fibre P Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard` using `fun y => by rw [hfib y, hinj.injOn.encard_image]`. Use `⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩` and prove the remaining obligations. Use `measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Take `⟨hcount, hsec⟩` from `hgen y h0`. Use `hy ⟨(henc y).trans hcount, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[hfib y]`. Take `⟨x, ⟨hxU, hxA⟩, rfl⟩` from `hw`. Take `⟨U, g, hUo, hyU, hg, hgy, hgU⟩` from `hsec x hxU hxA`.

Rewrite using `[← hgy]`. Use `hC K ι P e Ψ y (fun y' i' => g y' (σ.symm i')) hP.2.1.2.1 ?_` and prove the remaining obligations. Use `filter_upwards [hUo.mem_nhds hyU] with y' hy'`. Take `⟨hAg, J, hJF, hgJ⟩` from `hgU y' hy'`. Take `⟨z, hz, hzw, hΨz⟩` from `(mem_fibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩`.

Establish `hgd : DifferentiableAt ℂ g y'` using `hg.differentiableAt (hUo.mem_nhds hy')`. Conclude with `⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩`.
-/
theorem proof (hA : GoodChartModel.Statement) (hB : ComponentsGenericCount.Statement)
    (hC : SheetLift.Statement) : PtsGenericCount.Statement := by
  classical
  intro K _ ι _ P e Ψ hP hΨ
  set σ := (Fintype.equivFin ((k : K) → ι k)).symm
  obtain ⟨hZ, hJ⟩ := hA K ι P e _ σ Ψ hP hΨ
  set I := projChartIdeal P σ Ψ
  set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset
  set A := chartProjMatrix σ Ψ
  have hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes := fun J => Set.Finite.mem_toFinset _

  have hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ projChartSet P σ Ψ := by
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
  obtain ⟨hle, Δ, hΔ, hgen⟩ := hB _ e F A
    (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩)
    (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))

  have hfib : ∀ y, fibre P Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) ''
      {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} := by
    intro y
    ext w
    constructor
    · intro hw
      have hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w := by
        funext i'
        simp
      rw [← hw'] at hw
      obtain ⟨hxS, hxA⟩ := (mem_fibre_iff (P := P) σ Ψ y (fun a => w (σ a))).1 hw
      exact ⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact (mem_fibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩
  have hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) := by
    intro x x' h
    funext a
    simpa using congrFun h (σ a)
  have henc : ∀ y, (fibre P Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard :=
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
  refine hC K ι P e Ψ y (fun y' i' => g y' (σ.symm i')) hP.2.1.2.1 ?_
  filter_upwards [hUo.mem_nhds hyU] with y' hy'
  obtain ⟨hAg, J, hJF, hgJ⟩ := hgU y' hy'
  obtain ⟨z, hz, hzw, hΨz⟩ := (mem_fibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩
  have hgd : DifferentiableAt ℂ g y' := hg.differentiableAt (hUo.mem_nhds hy')
  exact ⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩

end PtsGenericCount

end GroundTheory.Heights₂.Heights
