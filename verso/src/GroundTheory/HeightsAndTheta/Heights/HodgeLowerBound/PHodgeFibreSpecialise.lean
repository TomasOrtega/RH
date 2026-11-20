import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D P τ b z wF wW hb hz hfib`. Take `⟨c', f', hb', hbspan⟩` from `hb`. Take `⟨c, f, bfr, g, lF, lW, hfr, hdom, hg, hlF, hlW, hspan, hF, hW⟩` from `hfib`. Take `⟨b', R, R', Rz, R'z, hb'li, hb'span, hR, hR', hRz, hR'z, hRR⟩` from `hT II Ψ K ι Ω E D τ c f bfr z hz hfr hdom`. Establish `hRdet : Rz.det ≠ 0` using `fun h0 => by`.

Use `congrArg Matrix.det hRR` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`. Establish `hZ : (∏ k, z ⟨k, c k⟩ ^ P.b k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hdom.1 k)`. Establish `htw : twistFactor D.y c P.b ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hfr.1 k (Finset.mem_univ _))`.

Establish `hli` using `hb'.2.2.2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (jIdx D).isLt) = u '' {i | (i : ℕ) < D.j}`. Introduce `u`. Use extensionality with `e`.

Simplify using `only [Set.mem_range, Function.comp_apply, Set.mem_image, Set.mem_setOf_eq]`. Establish `h1` using `D.one_le_j`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨_, by rw [Fin.val_castLE]; have := a.isLt; simp only [jIdx] at this; omega, rfl⟩`.

Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨⟨i, by simp only [jIdx]; omega⟩, rfl⟩`. Take `⟨M, hM, hMdet⟩` from `hC D.N _ (jIdx D).isLt Rz g hRdet hg ((hspan.trans (hS II Ψ K ι Ω E D τ bfr b' R R' Rz R'z z hz hfr.2.2.2.1 hb'li hb'span hR hR' hRz hR'z)).le)`. Take `⟨δ, hδ, hδφ⟩` from `hD Ω (E τ) _ (b ∘ Fin.castLE (jIdx D).isLt) (b' ∘ Fin.castLE (jIdx D).isLt) (hli.comp _ (Fin.castLE_injective _)) (hb'li.comp _ (Fin.castLE_injective _)) (by rw [hrange, hrange, hbspan, hb'span])`. Use `⟨δ * (twistFactor D.y c P.b)⁻¹, lF * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw), mul_ne_zero (mul_ne_zero hlF hMdet) hZ, fun m => ?_⟩` and prove the remaining obligations.

Take `⟨v, ⟨V, hV, rfl⟩, hwF⟩` from `hF m`. Take `⟨hV0, hVσ, w, hw, hsum⟩` from `hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (jIdx D) m) bfr z V (fun p a => R p (Fin.castLE (jIdx D).isLt a)) (firstCols Rz _ (jIdx D).isLt) hz hV (fun p a => hRz _ _)`. Use `⟨_, w, ?_, hw, ?_⟩` and prove the remaining obligations. Establish `he : (fun a => ∑ q, R q (Fin.castLE (jIdx D).isLt a) • bfr q) = b' ∘ Fin.castLE (jIdx D).isLt`. Use function extensionality and compare the values at `fun a => (hR _).symm`.

Rewrite using `[hδφ, he]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hwF, hM, hA D.N _ V _ M hV0 hVσ, hsum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN : D.N ≤ (lastIdx D : ℕ) + 1` using `by simp only [lastIdx]; omega`.

Establish `hsurj : Function.Surjective (Fin.castLE (lastIdx D).isLt)` using `fun i => ⟨⟨i, lt_of_lt_of_le i.isLt hN⟩, rfl⟩`. Establish `hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (lastIdx D).isLt) = Set.range u`. Introduce `u`. Rewrite using `[Set.range_comp, hsurj.range_eq, Set.image_univ]`. Take `⟨M, hM, hMdet⟩` from `hC' D.N _ (lastIdx D).isLt g hN hg`.

Take `⟨δ, hδ, hδφ⟩` from `hD Ω (E τ) _ (b ∘ Fin.castLE (lastIdx D).isLt) (bfr ∘ Fin.castLE (lastIdx D).isLt) (hli.comp _ (Fin.castLE_injective _)) (hfr.2.2.2.1.comp _ (Fin.castLE_injective _)) (by rw [hrange, hrange, hTop K ι Ω (E τ) D.N D.y (D.W τ) c' f' b hb', hTop K ι Ω (E τ) D.N D.y (D.W τ) c f bfr hf …`. Use `⟨δ * (twistFactor D.y c P.b)⁻¹, lW * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw), mul_ne_zero (mul_ne_zero hlW hMdet) hZ, fun m => ?_⟩` and prove the remaining obligations. Take `⟨v, ⟨V, hV, rfl⟩, hwW⟩` from `hW m`. Establish `h1 : ∀ p a, IsValueAt D.y ((1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) z (firstCols (1 : Matrix (Fin D.N) (Fin D.N) ℂ) _ (lastIdx D).isLt p a)`. Introduce `p a`.

Simplify using `only [firstCols, Matrix.one_apply]`. Use `split_ifs`. Use `exacts [isValueAt_one_self _ _, LineFlag.isValueAt_zero' _ _]`. Take `⟨hV0, hVσ, w, hw, hsum⟩` from `hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (lastIdx D) m) bfr z V (fun p a => (1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) _ hz hV h1`. Use `⟨_, w, ?_, hw, ?_⟩` and prove the remaining obligations.

Establish `he : (fun a => ∑ q, (1 : Matrix (Fin D.N) (Fin D.N) Ω) q (Fin.castLE (lastIdx D).isLt a) • bfr q) = bfr ∘ Fin.castLE (lastIdx D).isLt` using `funext fun a => by simp [Matrix.one_apply]`. Rewrite using `[hδφ, he]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hwW, hM, hA D.N _ V _ M hV0 hVσ, hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HodgeFibreSpecialise.proof (hT : HodgeFrameTransition.Statement) (hS : HodgeFibreSpan.Statement)
    (hC : ColSpanFactor.Statement) (hC' : FullColsFactor.Statement) (hA : AltSumDet.Statement)
    (hP : PlueckerExpand.Statement) (hD : SameSpanAltDet.Statement) (hTop : FrameSpanTop.Statement) :
    HodgeFibreSpecialise.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D P τ b z wF wW hb hz hfib
  obtain ⟨c', f', hb', hbspan⟩ := hb
  obtain ⟨c, f, bfr, g, lF, lW, hfr, hdom, hg, hlF, hlW, hspan, hF, hW⟩ := hfib
  obtain ⟨b', R, R', Rz, R'z, hb'li, hb'span, hR, hR', hRz, hR'z, hRR⟩ :=
    hT II Ψ K ι Ω E D τ c f bfr z hz hfr hdom
  have hRdet : Rz.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hRR
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hZ : (∏ k, z ⟨k, c k⟩ ^ P.b k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hdom.1 k)
  have htw : twistFactor D.y c P.b ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
    zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hfr.1 k (Finset.mem_univ _))
  have hli := hb'.2.2.2.1
  refine ⟨?_, ?_⟩
  · have hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (jIdx D).isLt) = u '' {i | (i : ℕ) < D.j} := by
      intro u
      ext e
      simp only [Set.mem_range, Function.comp_apply, Set.mem_image, Set.mem_setOf_eq]
      have h1 := D.one_le_j
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, by rw [Fin.val_castLE]; have := a.isLt; simp only [jIdx] at this; omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by simp only [jIdx]; omega⟩, rfl⟩
    obtain ⟨M, hM, hMdet⟩ := hC D.N _ (jIdx D).isLt Rz g hRdet hg
      ((hspan.trans (hS II Ψ K ι Ω E D τ bfr b' R R' Rz R'z z hz hfr.2.2.2.1 hb'li hb'span hR hR' hRz hR'z)).le)
    obtain ⟨δ, hδ, hδφ⟩ := hD Ω (E τ) _ (b ∘ Fin.castLE (jIdx D).isLt) (b' ∘ Fin.castLE (jIdx D).isLt)
      (hli.comp _ (Fin.castLE_injective _)) (hb'li.comp _ (Fin.castLE_injective _))
      (by rw [hrange, hrange, hbspan, hb'span])
    refine ⟨δ * (twistFactor D.y c P.b)⁻¹, lF * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw),
      mul_ne_zero (mul_ne_zero hlF hMdet) hZ, fun m => ?_⟩
    obtain ⟨v, ⟨V, hV, rfl⟩, hwF⟩ := hF m
    obtain ⟨hV0, hVσ, w, hw, hsum⟩ := hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (jIdx D) m) bfr z V
      (fun p a => R p (Fin.castLE (jIdx D).isLt a)) (firstCols Rz _ (jIdx D).isLt) hz hV (fun p a => hRz _ _)
    refine ⟨_, w, ?_, hw, ?_⟩
    · have he : (fun a => ∑ q, R q (Fin.castLE (jIdx D).isLt a) • bfr q) = b' ∘ Fin.castLE (jIdx D).isLt :=
        funext fun a => (hR _).symm
      rw [hδφ, he]
      field_simp
    · rw [hwF, hM, hA D.N _ V _ M hV0 hVσ, hsum]
      ring
  · have hN : D.N ≤ (lastIdx D : ℕ) + 1 := by simp only [lastIdx]; omega
    have hsurj : Function.Surjective (Fin.castLE (lastIdx D).isLt) := fun i =>
      ⟨⟨i, lt_of_lt_of_le i.isLt hN⟩, rfl⟩
    have hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (lastIdx D).isLt) = Set.range u := by
      intro u
      rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    obtain ⟨M, hM, hMdet⟩ := hC' D.N _ (lastIdx D).isLt g hN hg
    obtain ⟨δ, hδ, hδφ⟩ := hD Ω (E τ) _ (b ∘ Fin.castLE (lastIdx D).isLt) (bfr ∘ Fin.castLE (lastIdx D).isLt)
      (hli.comp _ (Fin.castLE_injective _)) (hfr.2.2.2.1.comp _ (Fin.castLE_injective _))
      (by rw [hrange, hrange, hTop K ι Ω (E τ) D.N D.y (D.W τ) c' f' b hb',
        hTop K ι Ω (E τ) D.N D.y (D.W τ) c f bfr hfr])
    refine ⟨δ * (twistFactor D.y c P.b)⁻¹, lW * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw),
      mul_ne_zero (mul_ne_zero hlW hMdet) hZ, fun m => ?_⟩
    obtain ⟨v, ⟨V, hV, rfl⟩, hwW⟩ := hW m
    have h1 : ∀ p a, IsValueAt D.y ((1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) z
        (firstCols (1 : Matrix (Fin D.N) (Fin D.N) ℂ) _ (lastIdx D).isLt p a) := by
      intro p a
      simp only [firstCols, Matrix.one_apply]
      split_ifs
      exacts [isValueAt_one_self _ _, LineFlag.isValueAt_zero' _ _]
    obtain ⟨hV0, hVσ, w, hw, hsum⟩ := hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (lastIdx D) m) bfr z V
      (fun p a => (1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) _ hz hV h1
    refine ⟨_, w, ?_, hw, ?_⟩
    · have he : (fun a => ∑ q, (1 : Matrix (Fin D.N) (Fin D.N) Ω) q (Fin.castLE (lastIdx D).isLt a) • bfr q) =
          bfr ∘ Fin.castLE (lastIdx D).isLt := funext fun a => by simp [Matrix.one_apply]
      rw [hδφ, he]
      field_simp
    · rw [hwW, hM, hA D.N _ V _ M hV0 hVσ, hsum]
      ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
