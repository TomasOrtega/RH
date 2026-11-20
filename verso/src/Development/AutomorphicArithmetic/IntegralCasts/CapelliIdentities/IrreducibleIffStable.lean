import Mathlib

/- English proof (translation)
Introduce `H K _ _ n r hspan W hW`. Establish `hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W`. Introduce `A v hv`. Establish `hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K))`. Rewrite using `[hspan]`.

Conclude with `Submodule.mem_top`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Conclude with `hW g v hv`.

Consider the case `zero => rw [Matrix.zero_mulVec]`. Conclude with `W.zero_mem`. Consider the case `add x y _ _ hx hy => rw [Matrix.add_mulVec]`. Conclude with `W.add_mem hx hy`. Consider the case `smul c x _ hx => rw [Matrix.smul_mulVec]`.

Conclude with `W.smul_mem c hx`. Distinguish the cases in `hb : W = ⊥`. Conclude with `Or.inl hb`. Use `right`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hv0`. Establish `hi' : v i ≠ 0` using `hi`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `h` using `hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv`.

Establish `e : (Matrix.of fun a b => if b = i then w a / v i else 0 : Matrix (Fin n) (Fin n) K).mulVec v = w`. Use function extensionality and compare the values at `a`. Simplify using `[Matrix.mulVec, dotProduct, hi']`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable :
    ∀ {H K : Type} [inst : Group H] [inst_1 : Field K] {n : ℕ}
    (r : H →* Matrix (Fin n) (Fin n) K),
    Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) = ⊤ →
      ∀ (W : Submodule K (Fin n → K)),
        (∀ (g : H), ∀ v ∈ W, ((r : H → Matrix (Fin n) (Fin n) K) g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro H K _ _ n r hspan W hW
  have hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have e : (Matrix.of fun a b => if b = i then w a / v i else 0 :
        Matrix (Fin n) (Fin n) K).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [e] at h
