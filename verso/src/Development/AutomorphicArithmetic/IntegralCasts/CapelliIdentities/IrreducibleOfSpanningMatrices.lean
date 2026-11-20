import Mathlib

/- English proof (translation)
Introduce `K G ι _ _ _ f hf N hN`. Establish `key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N`. Introduce `A v hv`. Establish `hA : A ∈ Submodule.span K (Set.range f)` using `by rw [hf]; exact Submodule.mem_top`. Proceed by induction on `hA using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Conclude with `hN g v hv`. Consider the case `zero => rw [Matrix.zero_mulVec]`. Conclude with `N.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [Matrix.add_mulVec]`. Conclude with `N.add_mem hx hy`. Consider the case `smul a x _ hx => rw [Matrix.smul_mulVec]`. Conclude with `N.smul_mem a hx`. Distinguish the cases in `h : N = ⊥`.

Conclude with `Or.inl h`. Use `right`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hv0`. Establish `hi' : v i ≠ 0` using `hi`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `h1` using `key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv`. Establish `h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w`. Use function extensionality and compare the values at `a`.

Simplify using `[Matrix.mulVec, dotProduct, hi']`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top :
    ∀ {K G ι : Type} [inst : Field K] [inst_1 : Fintype ι]
    [DecidableEq ι] (f : G → Matrix ι ι K),
    Submodule.span K (Set.range f) = ⊤ →
      ∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, (f g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro K G ι _ _ _ f hf N hN
  have key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range f) := by rw [hf]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem a hx
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h1 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
    have h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [h2] at h1
