import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.AlgebraicInfinityType.InfinityType

open NumberField

namespace UpperTheory.RegAlgFam

/- English proof (translation)
Proceed by induction on `s using Quotient.inductionOn with | _ l =>`. Proceed by induction on `t using Quotient.inductionOn with | _ k =>`. Establish `hl : l.length = k.length` using `by simpa using h`. Use `⟨(l.zip k : List (α × α)), ?_, ?_⟩` and prove the remaining obligations. Simplify using `[List.map_fst_zip hl.le]`.

Simplify using `[List.map_snd_zip hl.ge]`.
-/
theorem exists_pairs {α : Type*} (s t : Multiset α) (h : s.card = t.card) :
    ∃ P : Multiset (α × α), P.map Prod.fst = s ∧ P.map Prod.snd = t := by
  induction s using Quotient.inductionOn with | _ l =>
  induction t using Quotient.inductionOn with | _ k =>
  have hl : l.length = k.length := by simpa using h
  refine ⟨(l.zip k : List (α × α)), ?_, ?_⟩
  · simp [List.map_fst_zip hl.le]
  · simp [List.map_snd_zip hl.ge]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ⟨ha, hr⟩, he⟩ τ`. Use `⟨he τ ▸ hr τ, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `ha τ z (he τ ▸ hz)`. Conclude with `⟨m, by rw [hm, add_comm]⟩`.

Introduce `h choose P h1 h2 using fun τ : F →+* ℂ => exists_pairs (μ τ) (μ (ComplexEmbedding.conjugate τ)) ((hc _).trans (hc _).symm)`. Establish `cc : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ` using `fun τ => star_star τ`. Set `g : (F →+* ℂ) → Prop` to `fun τ => (InfinitePlace.mk τ).embedding = τ`. Establish `hg : ∀ τ, g (ComplexEmbedding.conjugate τ) ↔ ¬ g τ`. Introduce `τ`.

Establish `hne : ComplexEmbedding.conjugate τ ≠ τ` using `fun e => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))) ⟨τ, ComplexEmbedding.isReal_iff.2 e, rfl⟩`. Simplify using `only [g, InfinitePlace.mk_conjugate_eq]`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Rewrite using `[e]`. Simplify using `[hne.symm]`.

Rewrite using `[e]`. Simplify using `[hne]`. Set `Q : (F →+* ℂ) → Multiset (ℂ × ℂ)` to `fun τ => if g τ then P τ else (P (ComplexEmbedding.conjugate τ)).map Prod.swap`. Establish `q1 : ∀ τ, (Q τ).map Prod.fst = μ τ`. Introduce `τ`.

Distinguish the cases in `e : g τ`. Simplify using `[Q, e, h1]`. Use `h2 (ComplexEmbedding.conjugate τ)` as an intermediate fact. Rewrite `this` using `[cc]`. Simplify `this` using `[Q, e, Multiset.map_map]`.

Establish `qc : ∀ τ, Q (ComplexEmbedding.conjugate τ) = (Q τ).map Prod.swap`. Introduce `τ`. Distinguish the cases in `e : g τ`. Establish `e' : ¬ g (ComplexEmbedding.conjugate τ)` using `fun x => (hg τ).1 x e`. Simplify using `only [Q, if_pos e, if_neg e', cc]`.

Simplify using `only [Q, if_neg e, if_pos ((hg τ).2 e), Multiset.map_map]`. Simplify using the standard rewrite rules. Use `⟨⟨Q, fun τ => by rw [← hc τ, ← q1 τ, Multiset.card_map], fun τ p hp => ?_, qc⟩, ⟨fun τ z hz => ?_, fun τ => ?_⟩, q1⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(h τ).2 p.1 (q1 τ ▸ Multiset.mem_map_of_mem _ hp)`. Establish `hp' : p.2 ∈ μ (ComplexEmbedding.conjugate τ)`.

Rewrite using `[← q1, qc]`. Conclude with `Multiset.mem_map.2 ⟨p.swap, Multiset.mem_map_of_mem _ hp, rfl⟩`. Take `⟨b, hb⟩` from `(h _).2 p.2 hp'`. Conclude with `⟨a - b, by rw [ha, hb]; push_cast; ring⟩`. Take `⟨m, hm⟩` from `(h τ).2 z (q1 τ ▸ hz)`.

Conclude with `⟨m, by rw [hm, add_comm]⟩`. Use `(h τ).1` as an intermediate fact. Rewrite `this` using `[← q1 τ]`. Then use the resulting hypothesis.
-/
theorem exists_iff {F : Type*} [Field F] [IsTotallyComplex F] {n : ℕ} (μ : (F →+* ℂ) → Multiset ℂ)
    (hc : ∀ τ, (μ τ).card = n) :
    (∃ t : Reformulated.AlgebraicInfinityType.InfinityType F n, t.IsRegularAlgebraic ∧ ∀ τ, t.exponents τ = μ τ) ↔
      ∀ τ, (μ τ).Nodup ∧ ∀ z ∈ μ τ, ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  classical
  constructor
  · rintro ⟨t, ⟨ha, hr⟩, he⟩ τ
    refine ⟨he τ ▸ hr τ, fun z hz => ?_⟩
    obtain ⟨m, hm⟩ := ha τ z (he τ ▸ hz)
    exact ⟨m, by rw [hm, add_comm]⟩
  · intro h
    choose P h1 h2 using fun τ : F →+* ℂ =>
      exists_pairs (μ τ) (μ (ComplexEmbedding.conjugate τ)) ((hc _).trans (hc _).symm)
    have cc : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    let g : (F →+* ℂ) → Prop := fun τ => (InfinitePlace.mk τ).embedding = τ
    have hg : ∀ τ, g (ComplexEmbedding.conjugate τ) ↔ ¬ g τ := by
      intro τ
      have hne : ComplexEmbedding.conjugate τ ≠ τ := fun e =>
        (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
          ⟨τ, ComplexEmbedding.isReal_iff.2 e, rfl⟩
      simp only [g, InfinitePlace.mk_conjugate_eq]
      rcases InfinitePlace.embedding_mk_eq τ with e | e
      · rw [e]; simp [hne.symm]
      · rw [e]; simp [hne]
    let Q : (F →+* ℂ) → Multiset (ℂ × ℂ) := fun τ =>
      if g τ then P τ else (P (ComplexEmbedding.conjugate τ)).map Prod.swap
    have q1 : ∀ τ, (Q τ).map Prod.fst = μ τ := by
      intro τ
      by_cases e : g τ
      · simp [Q, e, h1]
      · have := h2 (ComplexEmbedding.conjugate τ)
        rw [cc] at this
        simpa [Q, e, Multiset.map_map] using this
    have qc : ∀ τ, Q (ComplexEmbedding.conjugate τ) = (Q τ).map Prod.swap := by
      intro τ
      by_cases e : g τ
      · have e' : ¬ g (ComplexEmbedding.conjugate τ) := fun x => (hg τ).1 x e
        simp only [Q, if_pos e, if_neg e', cc]
      · simp only [Q, if_neg e, if_pos ((hg τ).2 e), Multiset.map_map]
        simp
    refine ⟨⟨Q, fun τ => by rw [← hc τ, ← q1 τ, Multiset.card_map], fun τ p hp => ?_, qc⟩,
      ⟨fun τ z hz => ?_, fun τ => ?_⟩, q1⟩
    · obtain ⟨a, ha⟩ := (h τ).2 p.1 (q1 τ ▸ Multiset.mem_map_of_mem _ hp)
      have hp' : p.2 ∈ μ (ComplexEmbedding.conjugate τ) := by
        rw [← q1, qc]
        exact Multiset.mem_map.2 ⟨p.swap, Multiset.mem_map_of_mem _ hp, rfl⟩
      obtain ⟨b, hb⟩ := (h _).2 p.2 hp'
      exact ⟨a - b, by rw [ha, hb]; push_cast; ring⟩
    · obtain ⟨m, hm⟩ := (h τ).2 z (q1 τ ▸ hz)
      exact ⟨m, by rw [hm, add_comm]⟩
    · have := (h τ).1
      rwa [← q1 τ] at this

end UpperTheory.RegAlgFam
