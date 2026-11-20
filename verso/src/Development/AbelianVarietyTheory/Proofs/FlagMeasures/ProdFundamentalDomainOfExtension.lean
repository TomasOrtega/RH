import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v`. Take `⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩` from `h2 v.2`. Take `⟨l₁, ⟨hl₁, hl₁D⟩, -⟩` from `h1 (v.1 + s)`. Establish `hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ` using `hl₁`. Use `⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0)` using `by simp`. Rewrite using `[e]`. Conclude with `Λ.add_mem hs hl₁'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show v.1 + (s + l₁) ∈ D₁`.

Rewrite using `[← add_assoc]`. Conclude with `hl₁D`. Conclude with `hl₂D`. Introduce and unpack `⟨m₁, m₂⟩ ⟨hm, hmD⟩`. Establish `hmD1 : v.1 + m₁ ∈ D₁` using `hmD.1`.

Establish `hmD2 : v.2 + m₂ ∈ D₂` using `hmD.2`. Establish `e2 : m₂ = l₂` using `(h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩`. Substitute `e2` using the available equality. Establish `hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ`. Use `Λ.sub_mem hm hs` as an intermediate fact.

Simplify using `using this`. Establish `e1 : m₁ - s = l₁` using `(h1 (v.1 + s)).unique ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩`. Establish `: m₁ = s + l₁` using `by rw [← e1]; abel`. Rewrite using `[this]`.
-/
theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
