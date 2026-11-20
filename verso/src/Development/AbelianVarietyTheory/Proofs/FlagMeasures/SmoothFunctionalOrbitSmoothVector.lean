import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfOrb

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r H _ _ _ B _ _ σ Λ hσ v hv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg, hF, hE⟩` from `hv g₀ hg₀`. Use `⟨U, fun g => Λ (F g), hU, hg, (Λ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩` and prove the remaining obligations.

Introduce `g hgU hgH`. Conclude with `congrArg Λ (hE g hgU hgH)`. Introduce `ws`. Proceed by induction on `ws with`. Consider the case `nil => intro _ x _`.

Both sides reduce to the same expression. Consider the case `cons X w ih`. Introduce `hws x hx`. Establish `hX : InLieHpk k r X` using `hws X List.mem_cons_self`. Establish `hw : ∀ Y ∈ w, InLieHpk k r Y` using `fun Y hY => hws Y (List.mem_cons_of_mem _ hY)`.

Establish `hd` using `Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv w hw hX`. Establish `h2` using `((Λ.comp (σ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Establish `e : (fun t : ℝ => rdWord w (fun g : Mat k r => Λ (σ g v)) (x * NormedSpace.exp ((t : ℂ) • X))) = (⇑((Λ.comp (σ x)).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ w v))`. Use function extensionality and compare the values at `t`. Establish `ht` using `Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t`.

Rewrite using `[ih hw _ (GlobalTheory.SgInfDD.gg_mul hx ht)]`. Simplify using `only [Function.comp, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply]`. Rewrite using `[hσ.1.2 x hx _ ht]`. Both sides reduce to the same expression. Use `show deriv _ 0 = _`.

Rewrite using `[e, h2.deriv]`. Both sides reduce to the same expression.
-/
theorem smooth_rdWord_functional : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H))
    (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v →
    SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧
    ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r,
      rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  intro k r H _ _ _ B _ _ σ Λ hσ v hv
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg, hF, hE⟩ := hv g₀ hg₀
    refine ⟨U, fun g => Λ (F g), hU, hg, (Λ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hgH
    exact congrArg Λ (hE g hgU hgH)
  · intro ws
    induction ws with
    | nil => intro _ x _; rfl
    | cons X w ih =>
      intro hws x hx
      have hX : InLieHpk k r X := hws X List.mem_cons_self
      have hw : ∀ Y ∈ w, InLieHpk k r Y := fun Y hY => hws Y (List.mem_cons_of_mem _ hY)
      have hd := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv w hw hX
      have h2 := ((Λ.comp (σ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      have e : (fun t : ℝ => rdWord w (fun g : Mat k r => Λ (σ g v)) (x * NormedSpace.exp ((t : ℂ) • X))) =
          (⇑((Λ.comp (σ x)).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ w v)) := by
        funext t
        have ht := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t
        rw [ih hw _ (GlobalTheory.SgInfDD.gg_mul hx ht)]
        simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply]
        rw [hσ.1.2 x hx _ ht]
        rfl
      show deriv _ 0 = _
      rw [e, h2.deriv]
      rfl

end GlobalTheory.SgInfOrb
