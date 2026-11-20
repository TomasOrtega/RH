import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hc δ hδ hs`. Establish `key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c`. Introduce `w`. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Establish `hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x)` using `hc.2.2.2`.

Use `set z : ℂ := τ.1 δ with hz`. Establish `hstar : star z = -z`. Rewrite using `[hz, ← hconj, hs, map_neg]`. Establish `hre : z.re = 0`. Use `congrArg Complex.re hstar` as an intermediate fact.

Simplify using `only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz0 : z ≠ 0`. Rewrite using `[hz]`. Conclude with `(map_ne_zero τ.1).2 hδ`.

Establish `him : z.im ≠ 0` using `fun h => hz0 (Complex.ext hre h)`. Establish `hI : Complex.I * z = ((-z.im : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Break down `lt_or_gt_of_ne him with h | h` into its components or cases. Conclude with `⟨τ, -z.im, by linarith, hI⟩`.

Use `⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ τ.2` and prove the remaining obligations. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `: (τ.1.comp (σ : E →+* E)) δ = -z`.

Simplify using `[hs, hz]`. Rewrite using `[this, mul_neg, hI]`. Simplify using the standard rewrite rules. Use `choose emb hemb using key`. Conclude with `⟨emb, hemb⟩`.
-/
theorem posEx : PosEx := by
  intro F E _ _ _ _ _ σ hc δ hδ hs
  have key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x) := hc.2.2.2
    set z : ℂ := τ.1 δ with hz
    have hstar : star z = -z := by
      rw [hz, ← hconj, hs, map_neg]
    have hre : z.re = 0 := by
      have := congrArg Complex.re hstar
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      rw [hz]
      exact (map_ne_zero τ.1).2 hδ
    have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hre h)
    have hI : Complex.I * z = ((-z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨τ, -z.im, by linarith, hI⟩
    · refine ⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩
      · refine Eq.trans ?_ τ.2
        ext x
        simp
      · have : (τ.1.comp (σ : E →+* E)) δ = -z := by
          simp [hs, hz]
        rw [this, mul_neg, hI]
        simp
  choose emb hemb using key
  exact ⟨emb, hemb⟩

end UpperTheory.Gal.TP.Skew

end
