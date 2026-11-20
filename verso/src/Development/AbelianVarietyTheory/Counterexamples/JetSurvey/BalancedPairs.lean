import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

set_option autoImplicit false

namespace GlobalTheory.ChartJoints

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj]`. Both sides reduce to the same expression.
-/
theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

/- English proof (translation)
Establish `: ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hne` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))` to reduce the goal to its premises.

Use extensionality with `a`. Use `congrArg (fun z : c.F => (z : ℂ)) (hcon a)` as an intermediate fact. Simplify using `only [embK_coe] at this`. Rewrite `this` using `[emb_bar]`. Conclude with `this`.

Take `⟨a, ha⟩` from `this`. Establish `hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a)))` using `(IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[map_sub, sub_mul, hv a, sub_self, mul_zero]`.
-/
theorem balanced_pairs (H : Host E) {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S]
    (τ τ' : E →+* ℂ) (v : S)
    (hv : ∀ a : 𝓞 E, algebraMap c.F S (embK c τ a) * v = algebraMap c.F S (embK c τ' (H.bar a)) * v)
    (hne : τ ≠ ComplexEmbedding.conjugate τ') : v = 0 := by
  have : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    have := congrArg (fun z : c.F => (z : ℂ)) (hcon a)
    simp only [embK_coe] at this
    rw [emb_bar] at this
    exact this
  obtain ⟨a, ha⟩ := this
  have hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a))) :=
    (IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hv a, sub_self, mul_zero]

end GlobalTheory.ChartJoints
