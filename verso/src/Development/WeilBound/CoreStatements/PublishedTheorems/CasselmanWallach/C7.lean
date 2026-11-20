import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N`. Take `⟨m, K, I0, hK0, hmax⟩` from `hMax n ε (kfin ε σ) E hM N`. Take `⟨S, C', hS, hC', hbd⟩` from `hC4 n ε H σ hU hI hD E hKD m`. Use `⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩` and prove the remaining obligations. Introduce `e he`.

Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 he`. Conclude with `x.2`. Introduce `F hcont hder hgrow B hB hI0 v hv`. Set `F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ` to `F ∘ₗ (kfin ε σ).subtype`. Establish `key` using `hmax F' (fun w => hcont w w.2) (fun X hX w g hg => by`.

Establish `h1` using `hder X hX.1 w w.2 g hg`. Use `show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X))) (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0`. Rewrite using `[hKD X hX.1 w]`. Conclude with `h1)`. Use the proof step `(fun w => hgrow w w.2) B hB`.

Use the proof step `(fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
