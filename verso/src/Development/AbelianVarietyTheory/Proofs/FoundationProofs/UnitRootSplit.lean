import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ ι t D ht hD`. Take `⟨s, hs⟩` from `IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4 * D) (n := 2) (by norm_num)`. Establish `hsum : (t + s) / 2 + (t - s) / 2 = t` using `by ring`. Establish `hprod : (t + s) / 2 * ((t - s) / 2) = D`. Establish `: (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4` using `by ring`.

Rewrite using `[this, hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ a b : ℂ, a + b = t → a * b = D → 1 ≤ ‖ι.symm a‖ → ‖ι.symm a‖ = 1 ∧ ‖ι.symm b‖ = ‖ι.symm D‖`. Introduce `a b hab hmul ha`. Establish `hmulN : ‖ι.symm a‖ * ‖ι.symm b‖ = ‖ι.symm D‖`.

Rewrite using `[← norm_mul, ← map_mul, hmul]`. Establish `hb : ‖ι.symm b‖ < 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `: 1 ≤ ‖ι.symm a‖ * ‖ι.symm b‖` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hta : ι.symm a = ι.symm t + (-ι.symm b)`. Rewrite using `[← hab, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : ‖ι.symm t‖ ≠ ‖-ι.symm b‖` using `by rw [norm_neg, ht]; exact (ne_of_lt hb).symm`.

Establish `ha1 : ‖ι.symm a‖ = 1`. Rewrite using `[hta, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, ht]`. Conclude with `max_eq_left hb.le`. Use `⟨ha1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmulN, ha1, one_mul]`.

Establish `hmax : 1 ≤ max ‖ι.symm ((t + s) / 2)‖ ‖ι.symm ((t - s) / 2)‖`. Use `IsUltrametricDist.norm_add_le_max (ι.symm ((t + s) / 2)) (ι.symm ((t - s) / 2))` as an intermediate fact. Rewrite `this` using `[← map_add, hsum, ht]`. Conclude with `this`. Break down `le_max_iff.mp hmax with h | h` into its components or cases.

Take `⟨h1, h2⟩` from `key _ _ hsum hprod h`. Conclude with `⟨_, _, hsum, hprod, h1, h2⟩`. Establish `hsum' : (t - s) / 2 + (t + s) / 2 = t` using `by rw [add_comm]; exact hsum`. Establish `hprod' : (t - s) / 2 * ((t + s) / 2) = D` using `by rw [mul_comm]; exact hprod`. Take `⟨h1, h2⟩` from `key _ _ hsum' hprod' h`.

Conclude with `⟨_, _, hsum', hprod', h1, h2⟩`.
-/
theorem unitRoot_split : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (t D : ℂ),
    ‖ι.symm t‖ = 1 → ‖ι.symm D‖ < 1 →
    ∃ α β : ℂ, α + β = t ∧ α * β = D ∧ ‖ι.symm α‖ = 1 ∧ ‖ι.symm β‖ = ‖ι.symm D‖ := by
  intro l _ ι t D ht hD
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4 * D) (n := 2) (by norm_num)
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by ring
  have hprod : (t + s) / 2 * ((t - s) / 2) = D := by
    have : (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have key : ∀ a b : ℂ, a + b = t → a * b = D → 1 ≤ ‖ι.symm a‖ →
      ‖ι.symm a‖ = 1 ∧ ‖ι.symm b‖ = ‖ι.symm D‖ := by
    intro a b hab hmul ha
    have hmulN : ‖ι.symm a‖ * ‖ι.symm b‖ = ‖ι.symm D‖ := by
      rw [← norm_mul, ← map_mul, hmul]
    have hb : ‖ι.symm b‖ < 1 := by
      by_contra h
      push_neg at h
      have : 1 ≤ ‖ι.symm a‖ * ‖ι.symm b‖ := by nlinarith
      linarith
    have hta : ι.symm a = ι.symm t + (-ι.symm b) := by
      rw [← hab, map_add]; ring
    have hne : ‖ι.symm t‖ ≠ ‖-ι.symm b‖ := by rw [norm_neg, ht]; exact (ne_of_lt hb).symm
    have ha1 : ‖ι.symm a‖ = 1 := by
      rw [hta, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, ht]
      exact max_eq_left hb.le
    refine ⟨ha1, ?_⟩
    rw [← hmulN, ha1, one_mul]
  have hmax : 1 ≤ max ‖ι.symm ((t + s) / 2)‖ ‖ι.symm ((t - s) / 2)‖ := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm ((t + s) / 2)) (ι.symm ((t - s) / 2))
    rw [← map_add, hsum, ht] at this
    exact this
  rcases le_max_iff.mp hmax with h | h
  · obtain ⟨h1, h2⟩ := key _ _ hsum hprod h
    exact ⟨_, _, hsum, hprod, h1, h2⟩
  · have hsum' : (t - s) / 2 + (t + s) / 2 = t := by rw [add_comm]; exact hsum
    have hprod' : (t - s) / 2 * ((t + s) / 2) = D := by rw [mul_comm]; exact hprod
    obtain ⟨h1, h2⟩ := key _ _ hsum' hprod' h
    exact ⟨_, _, hsum', hprod', h1, h2⟩

end GlobalTheory
