import Mathlib

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.RestrictScalarsSpan

/- English proof (translation)
Establish `key : ∀ a : A, j a * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))`. Introduce `a`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, hi, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨a * i, I.mul_mem_left a hi, map_mul j a i⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul l y _ hy => rw [mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ l hy`. Use `h.inductionOn b (motive := fun b => b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `key`. Introduce `l b hb`.

Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ l hb`. Introduce `b c hb hc`. Rewrite using `[add_mul]`. Conclude with `add_mem hb hc`.
-/
theorem mul_mem_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4} [Field K] [Field L]
    [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) (b x : B) (hx : x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) :
    b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
  have key : ∀ a : A, j a * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
    intro a
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨a * i, I.mul_mem_left a hi, map_mul j a i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul l y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ l hy
  refine h.inductionOn b
    (motive := fun b => b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) ?_ ?_ ?_ ?_
  · simp
  · exact key
  · intro l b hb
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ l hb
  · intro b c hb hc
    rw [add_mul]; exact add_mem hb hc

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = Submodule.span L ((j : A → B) '' (I : Set A))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span B ((j : A → B) '' (I : Set A))` using `hx`. Use `clear hx`.

Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span hy`. Consider the case `zero => exact zero_mem _`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `smul b y _ hy => exact mul_mem_span h I b y hy`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `Ideal.mem_map_of_mem j hi`.
-/
theorem restrictScalars_map_eq_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4}
    [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) :
    Submodule.restrictScalars L (Ideal.map j I) =
      Submodule.span L ((⇑(AlgHom.toLinearMap j) : A → B) ''
        (↑(Submodule.restrictScalars K I) : Set A)) := by
  change _ = Submodule.span L ((j : A → B) '' (I : Set A))
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Submodule.span B ((j : A → B) '' (I : Set A)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul b y _ hy => exact mul_mem_span h I b y hy
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.mem_map_of_mem j hi

end GlobalTheory.RestrictScalarsSpan
