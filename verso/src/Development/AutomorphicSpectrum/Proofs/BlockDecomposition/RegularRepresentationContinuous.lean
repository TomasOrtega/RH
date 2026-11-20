import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

/- English proof (translation)
Introduce `n _ _ μ _ V _ _ _ hU x`. Use `(hU n μ).1` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Set `g : G n → C(G n, G n)` to `fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩`. Establish `hg : Continuous g` using `ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)`.

Establish `hm : ∀ h, MeasurePreserving (g h) μ μ` using `fun h => measurePreserving_mul_right μ h`. Establish `key` using `Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm (by norm_num : (2 : ENNReal) ≠ ⊤)`. Use `key.congr fun h => ?_` and prove the remaining obligations. Establish `hm' : MeasurePreserving (fun y : G n => y * h) μ μ` using `measurePreserving_mul_right μ h`. Simplify using `only [rR, dif_pos hm']`.

Both sides reduce to the same expression. Set `g : G n → C(G n, G n)` to `fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩`. Establish `hg : Continuous g` using `ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)`. Establish `hm : ∀ y, MeasurePreserving (g y) μ μ` using `fun y => measurePreserving_mul_left μ y⁻¹`. Establish `key` using `Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm (by norm_num : (2 : ENNReal) ≠ ⊤)`.

Conclude with `key`.
-/
theorem translations_strongly_continuous :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod →
      ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧
        Continuous (fun y : G n => lT μ V y x) := by
  intro n _ _ μ _ V _ _ _ hU x
  have := (hU n μ).1
  constructor
  · let g : G n → C(G n, G n) := fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)
    have hm : ∀ h, MeasurePreserving (g h) μ μ := fun h => measurePreserving_mul_right μ h
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    refine key.congr fun h => ?_
    have hm' : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
    simp only [rR, dif_pos hm']
    rfl
  · let g : G n → C(G n, G n) := fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)
    have hm : ∀ y, MeasurePreserving (g y) μ μ := fun y => measurePreserving_mul_left μ y⁻¹
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact key

end GlobalTheory.CompanionTheory.PresSobA
