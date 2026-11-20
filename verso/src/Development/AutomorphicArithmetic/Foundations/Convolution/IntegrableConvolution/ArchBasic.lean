import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ m D n`. Take `⟨h1, h2, h3, h4, h5, -⟩` from `UpperTheory.ConvolutionTheory.L1.glueBasic (InfiniteAdeleRing F) (InfiniteAdeleRing E) _ _ m D n`. Establish `compA_apply : ∀ i x, UpperTheory.ConvolutionTheory.L1.compA D n i x = archEquiv F n (D.comp n i ((archEquiv E n).symm x))` using `fun _ _ => rfl`. Establish `glueA_apply : ∀ g, UpperTheory.ConvolutionTheory.L1.glueA D n g = archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))` using `fun _ => rfl`. Establish `c1 : ∀ g i, UpperTheory.ConvolutionTheory.L1.compA D n i (UpperTheory.ConvolutionTheory.L1.glueA D n g) = g i`.

Introduce `g i`. Rewrite using `[compA_apply, glueA_apply, ContinuousMulEquiv.symm_apply_apply, h1, ContinuousMulEquiv.apply_symm_apply]`. Establish `c2 : ∀ x, UpperTheory.ConvolutionTheory.L1.glueA D n (fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x) = x`. Introduce `x`. Rewrite using `[glueA_apply]`.

Simplify using `only [compA_apply, ContinuousMulEquiv.symm_apply_apply]`. Rewrite using `[h2, ContinuousMulEquiv.apply_symm_apply]`. Establish `c3 : ∀ g h, UpperTheory.ConvolutionTheory.L1.glueA D n (g * h) = UpperTheory.ConvolutionTheory.L1.glueA D n g * UpperTheory.ConvolutionTheory.L1.glueA D n h`. Introduce `g h`. Simplify using `only [glueA_apply]`.

Rewrite using `[← map_mul, ← h3]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `c4 : Continuous (UpperTheory.ConvolutionTheory.L1.glueA D n)`.

Establish `: Continuous fun g : Fin (m + 1) → archGroup F n => archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))` using `(archEquiv E n).continuous.comp (h4.comp (continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)))`. Conclude with `this`. Establish `c5 : ∀ i, Continuous (UpperTheory.ConvolutionTheory.L1.compA D n i)`. Introduce `i`. Establish `: Continuous fun x : archGroup E n => archEquiv F n (D.comp n i ((archEquiv E n).symm x))` using `(archEquiv F n).continuous.comp ((h5 i).comp (archEquiv E n).symm.continuous)`.

Conclude with `this`. Set `e : (Fin (m + 1) → archGroup F n) ≃ₜ* archGroup E n` to `{ toFun := UpperTheory.ConvolutionTheory.L1.glueA D n invFun := fun x i => UpperTheory.ConvolutionTheory.L1.compA D n i x left_inv := fun g => funext (c1 g) right_inv := c2 map_mul' := c3 continuous_toFun := c4 continuous_invFun := continuous_pi c5 }`. Use `⟨c1, c2, c3, c4, c5, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun i => (e.toMulEquiv.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (m + 1) => archGroup F n) i), ?_, ?_⟩` and prove the remaining obligations. Introduce `i g`.

Both sides reduce to the same expression. Introduce `i`. Establish `hm : Continuous fun g : archGroup F n => (Pi.mulSingle i g : Fin (m + 1) → archGroup F n)`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `using (continuous_id' : Continuous fun a : archGroup F n => a)`. Simplify `continuous_const` using `[Pi.mulSingle_eq_of_ne hj]`. Conclude with `c4.comp hm`. Introduce `νF _`.

Conclude with `e.isHaarMeasure_map (Measure.pi fun _ => νF)`. Introduce `φ`. Establish `hc : Continuous fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g)` using `continuous_finset_prod _ fun i _ => (φ i).continuous.comp (c5 i)`. Establish `hK : IsCompact (UpperTheory.ConvolutionTheory.L1.glueA D n '' Set.pi Set.univ fun i => tsupport (φ i))` using `(isCompact_univ_pi fun i => (φ i).hasCompactSupport).image c4`. Establish `hs : HasCompactSupport fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g)`.

Use `HasCompactSupport.of_support_subset_isCompact hK ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x, ?_, c2 x⟩` and prove the remaining obligations. Introduce `i _`. Apply `subset_tsupport` to reduce the goal to its premises.

Introduce `h0`. Conclude with `hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)`. Conclude with `⟨⟨⟨_, hc⟩, hs⟩, fun g => rfl⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.archBasic :
    UpperTheory.ConvolutionTheory.L1.ArchBasic := by
  intro F E _ _ _ _ _ σ m D n
  obtain ⟨h1, h2, h3, h4, h5, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (InfiniteAdeleRing F) (InfiniteAdeleRing E) _ _ m D n
  have compA_apply : ∀ i x, UpperTheory.ConvolutionTheory.L1.compA D n i x =
      archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  have glueA_apply : ∀ g, UpperTheory.ConvolutionTheory.L1.glueA D n g =
      archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) := fun _ => rfl
  have c1 : ∀ g i, UpperTheory.ConvolutionTheory.L1.compA D n i (UpperTheory.ConvolutionTheory.L1.glueA D n g) = g i := by
    intro g i
    rw [compA_apply, glueA_apply, ContinuousMulEquiv.symm_apply_apply, h1,
      ContinuousMulEquiv.apply_symm_apply]
  have c2 : ∀ x, UpperTheory.ConvolutionTheory.L1.glueA D n (fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x) = x := by
    intro x
    rw [glueA_apply]
    simp only [compA_apply, ContinuousMulEquiv.symm_apply_apply]
    rw [h2, ContinuousMulEquiv.apply_symm_apply]
  have c3 : ∀ g h, UpperTheory.ConvolutionTheory.L1.glueA D n (g * h) =
      UpperTheory.ConvolutionTheory.L1.glueA D n g * UpperTheory.ConvolutionTheory.L1.glueA D n h := by
    intro g h
    simp only [glueA_apply]
    rw [← map_mul, ← h3]
    congr 2
    funext i
    simp
  have c4 : Continuous (UpperTheory.ConvolutionTheory.L1.glueA D n) := by
    have : Continuous fun g : Fin (m + 1) → archGroup F n =>
        archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) :=
      (archEquiv E n).continuous.comp
        (h4.comp (continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)))
    exact this
  have c5 : ∀ i, Continuous (UpperTheory.ConvolutionTheory.L1.compA D n i) := by
    intro i
    have : Continuous fun x : archGroup E n =>
        archEquiv F n (D.comp n i ((archEquiv E n).symm x)) :=
      (archEquiv F n).continuous.comp ((h5 i).comp (archEquiv E n).symm.continuous)
    exact this
  let e : (Fin (m + 1) → archGroup F n) ≃ₜ* archGroup E n :=
    { toFun := UpperTheory.ConvolutionTheory.L1.glueA D n
      invFun := fun x i => UpperTheory.ConvolutionTheory.L1.compA D n i x
      left_inv := fun g => funext (c1 g)
      right_inv := c2
      map_mul' := c3
      continuous_toFun := c4
      continuous_invFun := continuous_pi c5 }
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_, ?_⟩
  · refine ⟨fun i => (e.toMulEquiv.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (m + 1) => archGroup F n) i), ?_, ?_⟩
    · intro i g
      rfl
    · intro i
      have hm : Continuous fun g : archGroup F n => (Pi.mulSingle i g : Fin (m + 1) → archGroup F n) :=
        by
          refine continuous_pi fun j => ?_
          by_cases hj : j = i
          · subst hj
            simpa using (continuous_id' : Continuous fun a : archGroup F n => a)
          · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
      exact c4.comp hm
  · intro νF _
    exact e.isHaarMeasure_map (Measure.pi fun _ => νF)
  · intro φ
    have hc : Continuous fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) :=
      continuous_finset_prod _ fun i _ => (φ i).continuous.comp (c5 i)
    have hK : IsCompact (UpperTheory.ConvolutionTheory.L1.glueA D n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (φ i).hasCompactSupport).image c4
    have hs : HasCompactSupport fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro x hx
      refine ⟨fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x, ?_, c2 x⟩
      intro i _
      apply subset_tsupport
      intro h0
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact ⟨⟨⟨_, hc⟩, hs⟩, fun g => rfl⟩
