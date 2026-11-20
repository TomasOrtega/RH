import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapAreaOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

/- English proof (translation)
Introduce `n e ι _ U D v F hUD hinj hF`. Set `g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n)` to `fun i q => q.2 • WithLp.toLp 2 (v i q.1)`. Set `S : ι → Set ((Fin e → ℂ) × ℂ)` to `fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}`. Establish `himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) '' {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨i, x, t⟩, hq, rfl⟩`. Conclude with `⟨i, (x, t), hq, rfl⟩`. Introduce and unpack `⟨i, ⟨x, t⟩, hq, rfl⟩`.

Conclude with `⟨(i, x, t), hq, rfl⟩`. Establish `hinj_i : ∀ i, Set.InjOn (g i) (S i)`. Introduce `i p hp p' hp' hpp`. Conclude with `(Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2`. Establish `hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i)`.

Introduce `i j hij`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩`. Conclude with `hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm`. Establish `hmeas : ∀ i, MeasurableSet (g i '' S i)`.

Introduce `i`. Take `⟨-, hD, hDU, hv⟩` from `hUD i`. Use `MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)` and prove the remaining obligations. Conclude with `(measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)`. Establish `hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i)` using `(PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)`.

Conclude with `continuousOn_snd.smul hc`. Rewrite using `[himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun i => ?_` and prove the remaining obligations. Take `⟨hU, hD, hDU, hv⟩` from `hUD i`. Conclude with `h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF`.
-/
theorem ConeMapArea.proof (h : ConeMapAreaOne.Statement) : ConeMapArea.Statement := by
  intro n e ι _ U D v F hUD hinj hF
  let g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n) := fun i q => q.2 • WithLp.toLp 2 (v i q.1)
  let S : ι → Set ((Fin e → ℂ) × ℂ) := fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}
  have himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, x, t⟩, hq, rfl⟩
      exact ⟨i, (x, t), hq, rfl⟩
    · rintro ⟨i, ⟨x, t⟩, hq, rfl⟩
      exact ⟨(i, x, t), hq, rfl⟩
  have hinj_i : ∀ i, Set.InjOn (g i) (S i) := by
    intro i p hp p' hp' hpp
    exact (Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2
  have hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩
    exact hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm
  have hmeas : ∀ i, MeasurableSet (g i '' S i) := by
    intro i
    obtain ⟨-, hD, hDU, hv⟩ := hUD i
    refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)
    · exact (measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)
    · have hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn
          ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)
      exact continuousOn_snd.smul hc
  rw [himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  obtain ⟨hU, hD, hDU, hv⟩ := hUD i
  exact h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF

end GroundTheory.Heights₂.Heights
