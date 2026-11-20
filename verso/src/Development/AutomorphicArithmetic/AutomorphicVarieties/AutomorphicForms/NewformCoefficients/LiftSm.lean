import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchSm

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf in
/- English proof (translation)
Introduce `k M hM f φ hφ`. Use `⟨fun γ g => ?_, fun u hu g => ?_, fun hf g => ?_⟩` and prove the remaining obligations. Take `⟨γ', h, u, hu, rfl⟩` from `decomp M hM g`. Rewrite using `[← mul_assoc, ← map_mul, hφ _ _ _ hu, hφ _ _ _ hu]`. Take `⟨γ', h, u', hu', rfl⟩` from `decomp M hM g`.

Rewrite using `[mul_assoc, mul_assoc, ← map_mul, hφ _ _ _ hu', hφ _ _ _ (mul_mem hu' hu)]`. Take `⟨γ, h, u, hu, rfl⟩` from `decomp M hM g`. Set `L : TR.Lie ℚ 2 → (Fin 2 → Fin 2 → ℝ)` to `fun x i j => ∑ l, h.val i l * x l j Rat.infinitePlace`. Establish `hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L`. Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun l _ => contDiff_const.mul ?_` and prove the remaining obligations.

Conclude with `(contDiff_apply ℝ _ Rat.infinitePlace).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))`. Establish `hLy : ∀ y : GL (Fin 2) (TR.Rinf ℚ), Matrix.of (L (TR.toL y.val)) = (h * Matrix.GeneralLinearGroup.map ev y).val` using `fun y => rfl`. Use `((archSm k f hf).comp hL.contDiffOn fun x hx => ?_).congr fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `id hx`. Establish `e : x = TR.toL y.val` using `hy.symm`.

Substitute `e` using the available equality. Express the relevant statement in the definitionally equal form `(Matrix.of (L (TR.toL y.val))).det ≠ 0`. Rewrite using `[hLy]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero`. Take `⟨y, hy⟩` from `id hx`.

Establish `e : x = TR.toL y.val` using `hy.symm`. Substitute `e` using the available equality. Rewrite using `[TR.chart_val, ← upR_ev, mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ _ _ _ hu, Function.comp_apply, arch, hLy]`.
-/
theorem UpperTheory.V.Af.Nf.liftSm :
    UpperTheory.V.Af.Nf.LiftSm := by
  intro k M hM f φ hφ
  refine ⟨fun γ g => ?_, fun u hu g => ?_, fun hf g => ?_⟩
  · obtain ⟨γ', h, u, hu, rfl⟩ := decomp M hM g
    rw [← mul_assoc, ← map_mul, hφ _ _ _ hu, hφ _ _ _ hu]
  · obtain ⟨γ', h, u', hu', rfl⟩ := decomp M hM g
    rw [mul_assoc, mul_assoc, ← map_mul, hφ _ _ _ hu', hφ _ _ _ (mul_mem hu' hu)]
  · obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
    let L : TR.Lie ℚ 2 → (Fin 2 → Fin 2 → ℝ) := fun x i j => ∑ l, h.val i l * x l j Rat.infinitePlace
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L := by
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun l _ => contDiff_const.mul ?_
      exact (contDiff_apply ℝ _ Rat.infinitePlace).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
    have hLy : ∀ y : GL (Fin 2) (TR.Rinf ℚ),
        Matrix.of (L (TR.toL y.val)) = (h * Matrix.GeneralLinearGroup.map ev y).val := fun y => rfl
    refine ((archSm k f hf).comp hL.contDiffOn fun x hx => ?_).congr fun x hx => ?_
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      change (Matrix.of (L (TR.toL y.val))).det ≠ 0
      rw [hLy]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      rw [TR.chart_val, ← upR_ev, mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ _ _ _ hu,
        Function.comp_apply, arch, hLy]
