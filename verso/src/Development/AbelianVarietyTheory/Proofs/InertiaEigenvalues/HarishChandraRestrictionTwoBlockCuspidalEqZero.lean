import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨0, by simp, fun h => absurd rfl h⟩`. Consider the case `cons p L ih`. Take `⟨n, hn, hp⟩` from `hf p (List.mem_cons_self ..)`. Take `⟨m, hm, -⟩` from `ih fun q hq => hf q (List.mem_cons_of_mem _ hq)`.

Use `⟨n + m, ?_, fun _ => by omega⟩` and prove the remaining obligations. Simplify using `[List.map_cons, List.sum_cons, hp, hm]`.
-/
theorem list_sum_posNat {ι : Type} (L : List ι) (f : ι → ℂ) (hf : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ f p = n) :
    ∃ m : ℕ, (L.map f).sum = m ∧ (L ≠ [] → 0 < m) := by
  induction L with
  | nil => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | cons p L ih =>
    obtain ⟨n, hn, hp⟩ := hf p (List.mem_cons_self ..)
    obtain ⟨m, hm, -⟩ := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    refine ⟨n + m, ?_, fun _ => by omega⟩
    simp [List.map_cons, List.sum_cons, hp, hm]

/- English proof (translation)
Introduce `g _ d a χ hχ ha had x y`. Take `⟨-, hirr, hc⟩` from `hχ`. Establish `hchar : IsChar χ`. Take `⟨V, -, hV⟩` from `hirr`. Conclude with `⟨V, hV⟩`.

Take `⟨L, hL, hres⟩` from `(GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a (d - a) d (by omega)).2 χ hchar`. Establish `hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n`. Introduce `p hp`. Take `⟨d₁, hd₁, h₁⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g a) 0 p.1).2.1 (hL p hp).1`. Take `⟨d₂, hd₂, h₂⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2`.

Conclude with `⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩`. Take `⟨m, hm, hmpos⟩` from `list_sum_posNat L _ hpos`. Establish `hL0 : L = []`. Assume the negation of the conclusion as `hne`. Establish `h0 : res a (d - a) χ 1 1 = 0` using `hc a ha had`.

Rewrite `h0` using `[hres, hm]`. Use `hmpos hne` as an intermediate fact. Conclude with `absurd (by exact_mod_cast h0 : m = 0) (by omega)`. Rewrite using `[hres, hL0]`. Simplify using the standard rewrite rules.
-/
theorem res_cusp_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d →
    ∀ x y, res a (d - a) χ x y = 0 := by
  intro g _ d a χ hχ ha had x y
  obtain ⟨-, hirr, hc⟩ := hχ
  have hchar : IsChar χ := by
    obtain ⟨V, -, hV⟩ := hirr
    exact ⟨V, hV⟩
  obtain ⟨L, hL, hres⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a (d - a) d (by omega)).2 χ hchar
  have hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n := by
    intro p hp
    obtain ⟨d₁, hd₁, h₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g a) 0 p.1).2.1 (hL p hp).1
    obtain ⟨d₂, hd₂, h₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2
    exact ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩
  obtain ⟨m, hm, hmpos⟩ := list_sum_posNat L _ hpos
  have hL0 : L = [] := by
    by_contra hne
    have h0 : res a (d - a) χ 1 1 = 0 := hc a ha had
    rw [hres, hm] at h0
    have := hmpos hne
    exact absurd (by exact_mod_cast h0 : m = 0) (by omega)
  rw [hres, hL0]
  simp

end GlobalTheory.GLq
