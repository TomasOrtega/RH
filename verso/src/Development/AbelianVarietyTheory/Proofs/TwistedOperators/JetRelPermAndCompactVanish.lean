import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => intro l₁ _`. Both sides reduce to the same expression. Consider the case `cons p _ ih`. Introduce `l₁ hl`.

Use `ih (l₁ ++ [p]) (by simpa using hl)` as an intermediate fact. Simplify using `using this`. Consider the case `swap p q l`. Introduce `l₁ hl`. Take `⟨a, b⟩` from `q`.

Take `⟨c, d⟩` from `p`. Establish `h1` using `hB.1 l₁ l a b c d`. Establish `hlen : ∀ r : Fin n × Fin n, B (l₁ ++ r :: l) = 0`. Introduce `r`. Apply `h0` to reduce the goal to its premises.

Simplify using `only [List.length_append, List.length_cons] at hl ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[hlen, hlen, ite_self, ite_self, sub_zero]`. Conclude with `sub_eq_zero.mp h1`. Consider the case `trans h₁ _ ih₁ ih₂`.

Introduce `l₁ hl`. Rewrite using `[ih₁ l₁ hl, ih₂ l₁ (by rw [← hl]; simp [h₁.length_eq])]`.
-/
theorem jetRel_perm_of_vanish_prefix {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} {j : W →ₗᵢ[ℂ] V}
    {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hB : JetRel ε E Λ u j B)
    (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    ∀ l₁ : List (Fin n × Fin n), (l₁ ++ l).length = m + 1 → B (l₁ ++ l) = B (l₁ ++ l') := by
  induction h with
  | nil => intro l₁ _; rfl
  | cons p _ ih =>
    intro l₁ hl
    have := ih (l₁ ++ [p]) (by simpa using hl)
    simpa using this
  | swap p q l =>
    intro l₁ hl
    obtain ⟨a, b⟩ := q
    obtain ⟨c, d⟩ := p
    have h1 := hB.1 l₁ l a b c d
    have hlen : ∀ r : Fin n × Fin n, B (l₁ ++ r :: l) = 0 := by
      intro r
      apply h0
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    rw [hlen, hlen, ite_self, ite_self, sub_zero] at h1
    exact sub_eq_zero.mp h1
  | trans h₁ _ ih₁ ih₂ =>
    intro l₁ hl
    rw [ih₁ l₁ hl, ih₂ l₁ (by rw [← hl]; simp [h₁.length_eq])]

/- English proof (translation)
Introduce `V W _ _ _ _ n ε E Λ u j B m hL hB h0`. Establish `hperm : ∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l'`. Introduce `l l' h hl`. Simplify `hl)` using `using jetRel_perm_of_vanish_prefix hB h0 h [] (by simpa`. Use `⟨hperm, ?_⟩` and prove the remaining obligations.

Introduce and unpack `l hl ⟨⟨a, b⟩, hp, hab⟩`. Establish `hpe` using `List.perm_cons_erase hp`. Establish `hlen : (l.erase (a, b)).length ≤ m`. Use `hpe.length_eq` as an intermediate fact. Simplify using `only [List.length_cons] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hperm _ _ hpe hl]`. Use extensionality with `y x`. Establish `hy : j y ∈ Formalism.REAL.kSpan ε E u`. Rewrite using `[← hL.2.2.2.2]`.

Conclude with `⟨y, rfl⟩`. Establish `hy2 : E b a (j y) ∈ Formalism.REAL.kSpan ε E u` using `compact_span_compact_stable ε E u b a hab.symm _ hy`. Rewrite `hy2` using `[← hL.2.2.2.2]`. Take `⟨y', hy'⟩` from `hy2`. Rewrite using `[hB.2.2.1 _ a b hab y y' x hy', h0 _ hlen]`.

Simplify using the standard rewrite rules.
-/
theorem jetRel_perm_and_compact_vanish :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → (∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) → (∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l') ∧ ∀ l : List (Fin n × Fin n), l.length = m + 1 → (∃ p ∈ l, ε p.1 = ε p.2) → B l = 0 := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hB h0
  have hperm : ∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l' := by
    intro l l' h hl
    simpa using jetRel_perm_of_vanish_prefix hB h0 h [] (by simpa using hl)
  refine ⟨hperm, ?_⟩
  rintro l hl ⟨⟨a, b⟩, hp, hab⟩
  classical
  have hpe := List.perm_cons_erase hp
  have hlen : (l.erase (a, b)).length ≤ m := by
    have := hpe.length_eq
    simp only [List.length_cons] at this
    omega
  rw [hperm _ _ hpe hl]
  ext y x
  have hy : j y ∈ Formalism.REAL.kSpan ε E u := by
    rw [← hL.2.2.2.2]; exact ⟨y, rfl⟩
  have hy2 : E b a (j y) ∈ Formalism.REAL.kSpan ε E u := compact_span_compact_stable ε E u b a hab.symm _ hy
  rw [← hL.2.2.2.2] at hy2
  obtain ⟨y', hy'⟩ := hy2
  rw [hB.2.2.1 _ a b hab y y' x hy', h0 _ hlen]
  simp

end GlobalTheory.SphJet
