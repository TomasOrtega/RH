import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ a Ξ χ G hG n e he q α`. Establish `hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v` using `fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v`. Use `⟨fun g => ?_, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h : 0 ≤ ptIp χ G e α α g` using `mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)`. Take `⟨h1, h2⟩` from `Complex.nonneg_iff.1 h`.

Conclude with `⟨_, h1, Complex.ext rfl h2.symm⟩`. Establish `h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0` using `fun I => by`. Establish `hev : ∀ g, ev (α fun i => e (I i)) g = 0` using `fun g => by`. Establish `h` using `h0 g`. Rewrite `h` using `[ptIp, mul_eq_zero]`.

Break down `h with h | h` into its components or cases. Simplify using `at h`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)`. Assume the negation of the conclusion as `hne`. Conclude with `(hG.pos.dotProduct_mulVec_pos hne).ne' h1`.

Rewrite using `[← sum_cmp (α fun i => e (I i))]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `: cmp j (α fun i => e (I i)) = 0` using `Subtype.ext (funext fun g => by`. Rewrite using `[Pf.cmp_ev, hev]`. Use the proof step `rfl)`.

Rewrite using `[this, TensorProduct.zero_tmul]`. Use `AlternatingMap.ext fun X => ?_` and prove the remaining obligations. Establish `hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j` using `funext fun i => he (X i)`. Establish `h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i)` using `by conv_lhs => rw [hX]`. Conclude with `α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)`.

Rewrite using `[h3, AlternatingMap.zero_apply]`. Use `Finset.sum_eq_zero fun I _ => ?_` and prove the remaining obligations. Rewrite using `[α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
