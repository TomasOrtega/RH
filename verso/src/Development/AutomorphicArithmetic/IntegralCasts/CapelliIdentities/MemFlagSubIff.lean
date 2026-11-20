import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi34.flagSub :
    {F : Type} →
      [inst : Field F] →
        {N : Type} →
          [inst_1 : AddCommGroup N] → [inst_2 : _root_.Module F N] → {n : ℕ} → Module.Basis (Fin n) F N → ℕ → Submodule F N :=
    fun {F : Type} [Field F] {N : Type} [AddCommGroup N] [_root_.Module F N] {n : ℕ} (b : Module.Basis (Fin n) F N)
        (i : ℕ) ↦
      Submodule.span F ((⇑b : Fin n → N) '' {j : Fin n | (↑j : ℕ) < i})

/- English proof (translation)
Introduce `F _ n i x`. Unfold `UpperTheory.Reformulated.B.Qi34.flagSub`. Rewrite using `[Module.Basis.mem_span_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h j hj`.

Assume the negation of the conclusion as `hx`. Establish `hmem : j ∈ ((Pi.basisFun F (Fin n)).repr x).support`. Rewrite using `[Finsupp.mem_support_iff, Pi.basisFun_repr]`. Conclude with `hx`. Establish `hlt : (j : ℕ) < i` using `h (Finset.mem_coe.mpr hmem)`.

Use linear arithmetic over natural numbers and integers. Introduce `h j hj`. Establish `hx : x j ≠ 0`. Use `Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)` as an intermediate fact. Rewrite `this` using `[Pi.basisFun_repr]`. Then use the resulting hypothesis.

Use `show (j : ℕ) < i`. Assume the negation of the conclusion as `hlt`. Conclude with `hx (h j (not_lt.mp hlt))`.
-/
theorem UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff :
    ∀ {F : Type} [inst : Field F] {n : ℕ} (i : ℕ) (x : Fin n → F),
      x ∈ UpperTheory.Reformulated.B.Qi34.flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ (j : Fin n), i ≤ (↑j : ℕ) → x j = (0 : F) := by
  intro F _ n i x
  unfold UpperTheory.Reformulated.B.Qi34.flagSub
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hx
    have hmem : j ∈ ((Pi.basisFun F (Fin n)).repr x).support := by
      rw [Finsupp.mem_support_iff, Pi.basisFun_repr]
      exact hx
    have hlt : (j : ℕ) < i := h (Finset.mem_coe.mpr hmem)
    omega
  · intro h j hj
    have hx : x j ≠ 0 := by
      have := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      rwa [Pi.basisFun_repr] at this
    show (j : ℕ) < i
    by_contra hlt
    exact hx (h j (not_lt.mp hlt))
