import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def AbMulNSt : Prop :=
  (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g))

namespace AbMulNSt

variable {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] {g n : ℕ}

/- English proof (translation)
Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[h k B g n hB hg hn]`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hn Nat.cast_zero`.
-/
theorem finite (h : AbMulNSt) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom)
    (hn : (n : k) ≠ 0) : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [h k B g n hB hg hn]
  refine pow_ne_zero _ ?_
  rintro rfl
  exact hn Nat.cast_zero

/- English proof (translation)
Establish `: Unique {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1}` using `⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (ht x.1 x.2)⟩`. Establish `h1` using `h k B g n hB hg hn`. Rewrite `h1` using `[Nat.card_unique]`. Apply the tactic sequence `rcases Nat.pow_eq_one.1 h1.symm with h3 | h3 <;> omega`.
-/
theorem dim_eq_zero (h : AbMulNSt) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom)
    (hn : (n : k) ≠ 0) (h2 : 2 ≤ n) (ht : ∀ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = 1 → x = 1) :
    g = 0 := by
  have : Unique {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} :=
    ⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (ht x.1 x.2)⟩
  have h1 := h k B g n hB hg hn
  rw [Nat.card_unique] at h1
  rcases Nat.pow_eq_one.1 h1.symm with h3 | h3 <;> omega

omit [IsAlgClosed k] in

/- English proof (translation)
Use `⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `inferInstanceAs (Smooth (𝟙 (Sp k)))`. Conclude with `inferInstanceAs (IsProper (𝟙 (Sp k)))`. Express the relevant statement in the definitionally equal form `GeometricallyConnected (𝟙 (Sp k))`. Use `⟨fun K _ y Z fst snd H => ?_⟩` and prove the remaining obligations.

Establish `: IsIso snd` using `H.isIso_snd_of_isIso`. Conclude with `snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous`. Conclude with `inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp k)))`. Establish `: Unique {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1}` using `⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (toUnit_unique _ _)⟩`. Rewrite using `[Nat.card_unique, mul_zero, pow_zero]`.
-/
theorem unit_case (n : ℕ) : IsAbelianScheme (𝟙_ (Over (Sp k))) ∧
    SmoothOfRelativeDimension 0 (𝟙_ (Over (Sp k))).hom ∧
    Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1} = n ^ (2 * 0) := by
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact inferInstanceAs (Smooth (𝟙 (Sp k)))
  · exact inferInstanceAs (IsProper (𝟙 (Sp k)))
  · change GeometricallyConnected (𝟙 (Sp k))
    refine ⟨fun K _ y Z fst snd H => ?_⟩
    have : IsIso snd := H.isIso_snd_of_isIso
    exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous
  · exact inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp k)))
  · have : Unique {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1} :=
      ⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (toUnit_unique _ _)⟩
    rw [Nat.card_unique, mul_zero, pow_zero]

end AbMulNSt

end GlobalTheory.Published
