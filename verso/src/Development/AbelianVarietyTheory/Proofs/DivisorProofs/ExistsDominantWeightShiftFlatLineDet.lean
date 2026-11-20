import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

/- English proof (translation)
Simplify using `only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢`. Apply the tactic sequence `split_ifs at hi hj ⊢ <;> omega`.
-/
theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

/- English proof (translation)
Introduce `E _ _ _ H Dw a n τ hD ha`. Use `⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0, ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j < Dw.mult ρ`. Establish `hi : i < Dw.mult ρ` using `lt_of_le_of_lt hij hj`. Establish `h1 : a (ρ, j) ≤ a (ρ, i)` using `hD.1 ρ hij`.

Take `⟨e, -⟩` from `flat_step Dw τ ρ i j hi hj`. Simplify using `only [if_pos hi, if_pos hj]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [if_neg hj]`. Conclude with `Nat.zero_le _`.

Establish `h1` using `ha ρ i hi`. Establish `h2` using `(flat_step Dw τ ρ i i hi hi).2`. Simplify using `only [if_pos hi]`. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `x`.

Break down `x with _ | ⟨ρ, i⟩` into its components or cases. Simplify using `[exZ, wtZ, wtOf_snd]`. Establish `h1` using `ha ρ i i.2`. Establish `h2` using `(flat_step Dw τ ρ i i i.2 i.2).2`. Simplify using `only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
