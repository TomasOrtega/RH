import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Set `Z : Herm E a` to `⟨1, IsSelfAdjoint.one _⟩`. Establish `hZ : ∀ k, adHerm k Z = Z` using `fun k => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `k.1 * 1 * star k.1 = 1`. Rewrite using `[mul_one]`. Conclude with `k.2.2)`.

Proceed by induction on `q with`. Consider the case `zero => exact fun ω h0 h1 => ⟨0, ω, h0, h1, fun _ i => i.elim0⟩`. Consider the case `succ q ih`. Introduce `ω h0 h1`. Distinguish the cases in `hc : ω.curryLeft Z = 0`.

Use `⟨q + 1, ω, h0, h1, fun X i hi => ?_⟩` and prove the remaining obligations. Establish `hi' : X i = Z` using `Subtype.ext hi`. Establish `key : ∀ Y : Fin (q + 1) → Herm E a, Y 0 = Z → ω Y = 0` using `fun Y hY => by`. Establish `h` using `DFunLike.congr_fun hc (Fin.tail Y)`. Establish `e : Matrix.vecCons Z (Fin.tail Y) = Y` using `by rw [← hY]; exact Fin.cons_self_tail Y`.

Rewrite using `[← e]`. Conclude with `h`. Distinguish the cases in `hi0 : (0 : Fin (q + 1)) = i`. Conclude with `key X (hi0 ▸ hi')`. Establish `h` using `ω.map_swap X hi0`.

Rewrite `h` using `[key _ (by simpa using hi')]`. Conclude with `neg_eq_zero.1 h.symm`. Use `ih _ hc fun k X => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ω (Matrix.vecCons Z _) = κ k (ω (Matrix.vecCons Z X))`. Rewrite using `[← h1]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]`.
-/
private theorem basic_of_ne_zero {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    (κ : Kinf E a → Module.End ℂ M) (q : ℕ) :
    ∀ ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M, ω ≠ 0 → IsCochain κ ω →
      ∃ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), ω ≠ 0 ∧ IsCochain κ ω ∧ IsBasic ω := by
  let Z : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have hZ : ∀ k, adHerm k Z = Z := fun k => Subtype.ext (by
    change k.1 * 1 * star k.1 = 1
    rw [mul_one]; exact k.2.2)
  induction q with
  | zero => exact fun ω h0 h1 => ⟨0, ω, h0, h1, fun _ i => i.elim0⟩
  | succ q ih =>
    intro ω h0 h1
    by_cases hc : ω.curryLeft Z = 0
    · refine ⟨q + 1, ω, h0, h1, fun X i hi => ?_⟩
      have hi' : X i = Z := Subtype.ext hi
      have key : ∀ Y : Fin (q + 1) → Herm E a, Y 0 = Z → ω Y = 0 := fun Y hY => by
        have h := DFunLike.congr_fun hc (Fin.tail Y)
        have e : Matrix.vecCons Z (Fin.tail Y) = Y := by rw [← hY]; exact Fin.cons_self_tail Y
        rw [← e]
        exact h
      by_cases hi0 : (0 : Fin (q + 1)) = i
      · exact key X (hi0 ▸ hi')
      · have h := ω.map_swap X hi0
        rw [key _ (by simpa using hi')] at h
        exact neg_eq_zero.1 h.symm
    · refine ih _ hc fun k X => ?_
      change ω (Matrix.vecCons Z _) = κ k (ω (Matrix.vecCons Z X))
      rw [← h1]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]

/- English proof (translation)
Introduce `E _ _ _ a M _ _ _ _ κ L h`. Break down `h with ⟨ω, h1, -, h0⟩ | ⟨q, ω, h1, -, h2⟩` into its components or cases. Conclude with `basic_of_ne_zero κ 0 ω h0 h1`. Use `basic_of_ne_zero κ _ ω (fun h => h2 0 (fun k X => by simp) ?_) h1` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `AlternatingMap.ext fun X => by simp [dCo_apply]`.
-/
theorem UpperTheory.V.Lit.Bor.basicEx :
    UpperTheory.V.Lit.Bor.BasicEx := by
  intro E _ _ _ a M _ _ _ _ κ L h
  rcases h with ⟨ω, h1, -, h0⟩ | ⟨q, ω, h1, -, h2⟩
  · exact basic_of_ne_zero κ 0 ω h0 h1
  · refine basic_of_ne_zero κ _ ω (fun h => h2 0 (fun k X => by simp) ?_) h1
    rw [h]
    exact AlternatingMap.ext fun X => by simp [dCo_apply]
