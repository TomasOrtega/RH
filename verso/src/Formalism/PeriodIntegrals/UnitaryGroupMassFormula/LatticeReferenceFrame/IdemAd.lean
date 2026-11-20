import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLiftOfSteps

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.Id

section Ad

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `exact HeightOneSpectrum.mem_adicCompletionIntegers F v`. Consider the case `simp [HeightOneSpectrum.mem_adicCompletionIntegers]`.
-/
theorem memO {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  first
    | exact Iff.rfl
    | exact HeightOneSpectrum.mem_adicCompletionIntegers F v
    | simp [HeightOneSpectrum.mem_adicCompletionIntegers]

def evA (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evA_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evA v a = a v := rfl

/- English proof (translation)
Use `first`. Consider the case `(ext v; exact h v)`. Consider the case `exact Subtype.ext (funext h)`. Consider the case `exact RestrictedProduct.ext h`.
-/
theorem eq_of_evA {a b : Af F} (h : ∀ v, evA v a = evA v b) : a = b := by
  first
    | (ext v; exact h v)
    | exact Subtype.ext (funext h)
    | exact RestrictedProduct.ext h

def mkA (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (hc : ∀ v, Valued.v (c v) ≤ 1) :
    Af F :=
  ⟨c, Filter.Eventually.of_forall fun v => memO.2 (hc v)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkA_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) (v : HeightOneSpectrum (𝓞 F)) : mkA c hc v = c v := rfl

/- English proof (translation)
Unfold `Formalism.UG.intAd`. Use `show ∀ v, mkA c hc v ∈ HeightOneSpectrum.adicCompletionIntegers F v`. Introduce `v`. Rewrite using `[mkA_apply]`. Conclude with `memO.2 (hc v)`.
-/
theorem mkA_mem (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) : mkA c hc ∈ Formalism.UG.intAd F := by
  unfold Formalism.UG.intAd
  show ∀ v, mkA c hc v ∈ HeightOneSpectrum.adicCompletionIntegers F v
  intro v
  rw [mkA_apply]
  exact memO.2 (hc v)

/- English proof (translation)
The claim follows from `memO.1 (natCast_mem _ g)`.
-/
theorem natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) :
    Valued.v ((g : ℕ) : v.adicCompletion F) ≤ 1 := memO.1 (natCast_mem _ g)

end Ad

/- English proof (translation)
Unfold `AdOfLoc LocIdem AdIdem`. Introduce `hL F _ _ g α β hg hα hβ`. Establish `hα' : ∀ v, Valued.v (α v) ≤ 1`. Introduce `v`. Establish `h0` using `(show ∀ v, α v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hα) v`.

Conclude with `memO.1 h0`. Establish `hβ' : ∀ v, Valued.v (β v) ≤ 1`. Introduce `v`. Establish `h0` using `(show ∀ v, β v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hβ) v`. Conclude with `memO.1 h0`.

Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₁ c₂ : v.adicCompletion F, Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧ (1 + (g : v.adicCompletion F) * α v) * (1 + (g : v.adicCompletion F) * c₁) ^ 2 - 2 * (1 + (g : v.adicCompletion F) * c₁) * ((g : v.adicCompletion F) * c₂) = 1 + (g : v.adicCompl …`. Introduce `v`. Distinguish the cases in `hv : Valued.v ((g : ℕ) : v.adicCompletion F) < 1`. Conclude with `hL F v g (α v) (β v) hg hv (hα' v) (hβ' v)`. Establish `h1 : Valued.v ((g : ℕ) : v.adicCompletion F) = 1` using `le_antisymm (natCast_le_one v g) (not_lt.mp hv)`.

Establish `hg0 : ((g : ℕ) : v.adicCompletion F) ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, map_zero]`. Conclude with `zero_ne_one h1`. Establish `hu : 1 + (g : v.adicCompletion F) * -((g : v.adicCompletion F))⁻¹ = 0`.

Rewrite using `[mul_neg, mul_inv_cancel₀ hg0, add_neg_cancel]`. Use `⟨-((g : v.adicCompletion F))⁻¹, 0, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Valuation.map_neg, map_inv₀, h1, inv_one]`. Rewrite using `[map_zero]`. Conclude with `zero_le'`.

Rewrite using `[hu]`. Simplify using the standard rewrite rules. Rewrite using `[hu]`. Simplify using the standard rewrite rules. Rewrite using `[hu]`.

Simplify using the standard rewrite rules. Use `choose c₁ c₂ h1 h2 e1 e2 e3 using key`. Use `⟨mkA c₁ h1, mkA c₂ h2, mkA_mem c₁ h1, mkA_mem c₂ h2, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `eq_of_evA` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat, evA_apply, mkA_apply]`. Conclude with `e1 v`. Apply `eq_of_evA` to reduce the goal to its premises. Introduce `v`. Simplify using `only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat, evA_apply, mkA_apply]`.

Conclude with `e2 v`. Apply `eq_of_evA` to reduce the goal to its premises. Introduce `v`. Simplify using `only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat, map_zero, evA_apply, mkA_apply]`. Conclude with `e3 v`.
-/
theorem adOfLoc : AdOfLoc := by
  unfold AdOfLoc LocIdem AdIdem
  intro hL F _ _ g α β hg hα hβ
  have hα' : ∀ v, Valued.v (α v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, α v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hα) v
    exact memO.1 h0
  have hβ' : ∀ v, Valued.v (β v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, β v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hβ) v
    exact memO.1 h0
  have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₁ c₂ : v.adicCompletion F,
      Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α v) * (1 + (g : v.adicCompletion F) * c₁) ^ 2
          - 2 * (1 + (g : v.adicCompletion F) * c₁) * ((g : v.adicCompletion F) * c₂)
        = 1 + (g : v.adicCompletion F) * c₁ ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2
        = -((g : v.adicCompletion F) * c₂) ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (1 + (g : v.adicCompletion F) * α v) * ((g : v.adicCompletion F) * c₂)
            * (1 + (g : v.adicCompletion F) * c₁)
          + (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2 = 0 := by
    intro v
    by_cases hv : Valued.v ((g : ℕ) : v.adicCompletion F) < 1
    · exact hL F v g (α v) (β v) hg hv (hα' v) (hβ' v)
    · have h1 : Valued.v ((g : ℕ) : v.adicCompletion F) = 1 :=
        le_antisymm (natCast_le_one v g) (not_lt.mp hv)
      have hg0 : ((g : ℕ) : v.adicCompletion F) ≠ 0 := by
        intro h
        rw [h, map_zero] at h1
        exact zero_ne_one h1
      have hu : 1 + (g : v.adicCompletion F) * -((g : v.adicCompletion F))⁻¹ = 0 := by
        rw [mul_neg, mul_inv_cancel₀ hg0, add_neg_cancel]
      refine ⟨-((g : v.adicCompletion F))⁻¹, 0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Valuation.map_neg, map_inv₀, h1, inv_one]
      · rw [map_zero]
        exact zero_le'
      · rw [hu]
        simp
      · rw [hu]
        simp
      · rw [hu]
        simp
  choose c₁ c₂ h1 h2 e1 e2 e3 using key
  refine ⟨mkA c₁ h1, mkA c₂ h2, mkA_mem c₁ h1, mkA_mem c₂ h2, ?_, ?_, ?_⟩
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e1 v
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e2 v
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      map_zero, evA_apply, mkA_apply]
    exact e3 v

end PI.ScRefExists.Id
