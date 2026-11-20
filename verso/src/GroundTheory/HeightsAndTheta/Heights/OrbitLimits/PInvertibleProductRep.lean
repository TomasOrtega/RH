import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

/- English proof (translation)
Set `A : Ideal B` to `{ carrier := {a : B | (a : Ω) * z ∈ Y} add_mem' := by`. Introduce `a c ha hc`. Use `show ((a + c : B) : Ω) * z ∈ Y`. Use `push_cast`. Rewrite using `[add_mul]`.

Conclude with `Y.add_mem ha hc`. Use the proof step `zero_mem' := by show ((0 : B) : Ω) * z ∈ Y`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c a ha`.

Use `show ((c * a : B) : Ω) * z ∈ Y`. Use `push_cast`. Rewrite using `[mul_assoc]`. Conclude with `hY c c.2 _ ha }`. Distinguish the cases in `hA : A = ⊤`.

Establish `h1 : (1 : B) ∈ A` using `hA ▸ Submodule.mem_top`. Establish `h2 : ((1 : B) : Ω) * z ∈ Y` using `h1`. Simplify using `using h2`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal A hA`. Take `⟨b, hb, hbz⟩` from `hz m hm`.

Conclude with `absurd (hle (show b ∈ A from hbz)) hb`.
-/
theorem InvertibleProductRep.mem_of_local {Ω : Type} [Field Ω] (B : Subring Ω) (Y : AddSubgroup Ω)
    (hY : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y) (z : Ω)
    (hz : ∀ m : Ideal B, m.IsMaximal → ∃ b : B, b ∉ m ∧ (b : Ω) * z ∈ Y) : z ∈ Y := by
  let A : Ideal B :=
    { carrier := {a : B | (a : Ω) * z ∈ Y}
      add_mem' := by
        intro a c ha hc
        show ((a + c : B) : Ω) * z ∈ Y
        push_cast
        rw [add_mul]
        exact Y.add_mem ha hc
      zero_mem' := by
        show ((0 : B) : Ω) * z ∈ Y
        simp
      smul_mem' := by
        intro c a ha
        show ((c * a : B) : Ω) * z ∈ Y
        push_cast
        rw [mul_assoc]
        exact hY c c.2 _ ha }
  by_cases hA : A = ⊤
  · have h1 : (1 : B) ∈ A := hA ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * z ∈ Y := h1
    simpa using h2
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨b, hb, hbz⟩ := hz m hm
    exact absurd (hle (show b ∈ A from hbz)) hb

/- English proof (translation)
Introduce `Ω _ B M N P η _ g h β δ β' δ' I J hβ hδ hβ' hδ' hM hN hP hloc x`. Establish `hβΩ : (β : Ω) ≠ 0` using `fun h0 => hβ (Subtype.ext (by rw [h0]; rfl))`. Establish `hβ'Ω : (β' : Ω) ≠ 0` using `fun h0 => hβ' (Subtype.ext (by rw [h0]; rfl))`. Establish `hne : ((β * β' : B) : Ω) ≠ 0` using `by push_cast; exact mul_ne_zero hβΩ hβ'Ω`. Establish `notin : ∀ (m : Ideal B), m.IsMaximal → ∀ a b c : B, a ∉ m → b ∉ m → c ∉ m → a * b * c ∉ m`.

Introduce `m hm a b c ha hb hc h0`. Break down `hm.isPrime.mem_or_mem h0 with h1 | h1` into its components or cases. Break down `hm.isPrime.mem_or_mem h1 with h2 | h2` into its components or cases. Conclude with `ha h2`. Conclude with `hb h2`.

Conclude with `hc h1`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Set `Y : AddSubgroup Ω` to `{ carrier := {w | ∃ y ∈ I * J, ((β * β' : B) : Ω) * w = ((δ * δ' : B) : Ω) * (y : Ω)} add_mem' := by`. Introduce and unpack `a c ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩`.

Use `⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at e₁ e₂ ⊢`. Take the linear combination `e₁ + e₂`. Use the proof step `zero_mem' := ⟨0, zero_mem _, by simp⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `a ⟨y, hy, e⟩`. Use `⟨-y, neg_mem hy, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at e ⊢`. Take the linear combination `-e }`. Establish `hYst : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y`.

Introduce and unpack `b hb z ⟨y, hy, e⟩`. Use `⟨⟨b, hb⟩ * y, (I * J).mul_mem_left _ hy, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at e ⊢`. Take the linear combination `b * e`. Establish `key : x ∈ Y`.

Use `InvertibleProductRep.mem_of_local B Y hYst x fun m hm => ?_` and prove the remaining obligations. Take `⟨i, ⟨⟨b₁, hb₁, hgM⟩, -⟩, ⟨⟨b₂, hb₂, hhN⟩, -⟩, ⟨-, hPz⟩⟩` from `hloc m hm`. Take `⟨b, c, hb, e⟩` from `hPz x hx`. Take `⟨u, hu, eu⟩` from `(hM _).1 hgM`. Take `⟨v, hv, ev⟩` from `(hN _).1 hhN`.

Use `⟨b₁ * b₂ * b, notin m hm _ _ _ hb₁ hb₂ hb, c * (u * v), (I * J).mul_mem_left _ (Ideal.mul_mem_mul hu hv), ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at e eu ev ⊢`. Take the linear combination `((β : Ω) * β' * b₁ * b₂) * e + ((c : Ω) * β' * b₂ * h i) * eu + ((c : Ω) * δ * u) * ev`. Take `⟨y, hy, e⟩` from `key`. Conclude with `⟨y, hy, by push_cast at e ⊢; linear_combination e⟩`.

Introduce and unpack `⟨y, hy, e⟩`. Establish `claim : ∀ r ∈ I * J, ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P`. Introduce `r hr`. Use `Submodule.mul_induction_on (C := fun r : B => ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P) hr ?_ ?_` and prove the remaining obligations. Introduce `u hu v hv`.

Establish `hp : (δ : Ω) * u / β ∈ M` using `(hM _).2 ⟨u, hu, by field_simp⟩`. Establish `hq : (δ' : Ω) * v / β' ∈ N` using `(hN _).2 ⟨v, hv, by field_simp⟩`. Establish `hpq : ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') ∈ P`. Use `InvertibleProductRep.mem_of_local B P hP _ fun m hm => ?_` and prove the remaining obligations. Take `⟨i, ⟨-, hMz⟩, ⟨-, hNz⟩, ⟨⟨b'', hb'', hgh⟩, -⟩⟩` from `hloc m hm`.

Take `⟨b, c, hb, e₁⟩` from `hMz _ hp`. Take `⟨b', c', hb', e₂⟩` from `hNz _ hq`. Use `⟨b * b' * b'', notin m hm _ _ _ hb hb' hb'', ?_⟩` and prove the remaining obligations. Establish `eq : ((b * b' * b'' : B) : Ω) * (((δ : Ω) * u / β) * ((δ' : Ω) * v / β')) = ((c * c' : B) : Ω) * ((b'' : Ω) * (g i * h i))`. Use `push_cast`.

Take the linear combination `((b' : Ω) * b'' * ((δ' : Ω) * v / β')) * e₁ + ((c : Ω) * b'' * g i) * e₂`. Rewrite using `[eq]`. Conclude with `hP _ (c * c').2 _ hgh`. Establish `: ((δ * δ' : B) : Ω) * ((u * v : B) : Ω) / ((β * β' : B) : Ω) = ((δ : Ω) * u / β) * ((δ' : Ω) * v / β')`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `hpq`. Introduce `a c ha hc`. Establish `: ((δ * δ' : B) : Ω) * ((a + c : B) : Ω) / ((β * β' : B) : Ω) = ((δ * δ' : B) : Ω) * (a : Ω) / ((β * β' : B) : Ω) + ((δ * δ' : B) : Ω) * (c : Ω) / ((β * β' : B) : Ω)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `P.add_mem ha hc`. Establish `hx : x = ((δ * δ' : B) : Ω) * (y : Ω) / ((β * β' : B) : Ω)`.

Rewrite using `[eq_div_iff hne]`. Move the coercions through the operations in `at e ⊢`. Take the linear combination `e`. Rewrite using `[hx]`. Conclude with `claim y hy`.
-/
theorem InvertibleProductRep.proof : InvertibleProductRep.Statement := by
  intro Ω _ B M N P η _ g h β δ β' δ' I J hβ hδ hβ' hδ' hM hN hP hloc x
  have hβΩ : (β : Ω) ≠ 0 := fun h0 => hβ (Subtype.ext (by rw [h0]; rfl))
  have hβ'Ω : (β' : Ω) ≠ 0 := fun h0 => hβ' (Subtype.ext (by rw [h0]; rfl))
  have hne : ((β * β' : B) : Ω) ≠ 0 := by push_cast; exact mul_ne_zero hβΩ hβ'Ω
  have notin : ∀ (m : Ideal B), m.IsMaximal → ∀ a b c : B, a ∉ m → b ∉ m → c ∉ m → a * b * c ∉ m := by
    intro m hm a b c ha hb hc h0
    rcases hm.isPrime.mem_or_mem h0 with h1 | h1
    · rcases hm.isPrime.mem_or_mem h1 with h2 | h2
      · exact ha h2
      · exact hb h2
    · exact hc h1
  constructor
  · intro hx
    let Y : AddSubgroup Ω :=
      { carrier := {w | ∃ y ∈ I * J, ((β * β' : B) : Ω) * w = ((δ * δ' : B) : Ω) * (y : Ω)}
        add_mem' := by
          rintro a c ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
          refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
          push_cast at e₁ e₂ ⊢
          linear_combination e₁ + e₂
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        neg_mem' := by
          rintro a ⟨y, hy, e⟩
          refine ⟨-y, neg_mem hy, ?_⟩
          push_cast at e ⊢
          linear_combination -e }
    have hYst : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y := by
      rintro b hb z ⟨y, hy, e⟩
      refine ⟨⟨b, hb⟩ * y, (I * J).mul_mem_left _ hy, ?_⟩
      push_cast at e ⊢
      linear_combination b * e
    have key : x ∈ Y := by
      refine InvertibleProductRep.mem_of_local B Y hYst x fun m hm => ?_
      obtain ⟨i, ⟨⟨b₁, hb₁, hgM⟩, -⟩, ⟨⟨b₂, hb₂, hhN⟩, -⟩, ⟨-, hPz⟩⟩ := hloc m hm
      obtain ⟨b, c, hb, e⟩ := hPz x hx
      obtain ⟨u, hu, eu⟩ := (hM _).1 hgM
      obtain ⟨v, hv, ev⟩ := (hN _).1 hhN
      refine ⟨b₁ * b₂ * b, notin m hm _ _ _ hb₁ hb₂ hb, c * (u * v),
        (I * J).mul_mem_left _ (Ideal.mul_mem_mul hu hv), ?_⟩
      push_cast at e eu ev ⊢
      linear_combination ((β : Ω) * β' * b₁ * b₂) * e + ((c : Ω) * β' * b₂ * h i) * eu +
        ((c : Ω) * δ * u) * ev
    obtain ⟨y, hy, e⟩ := key
    exact ⟨y, hy, by push_cast at e ⊢; linear_combination e⟩
  · rintro ⟨y, hy, e⟩
    have claim : ∀ r ∈ I * J, ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P := by
      intro r hr
      refine Submodule.mul_induction_on
        (C := fun r : B => ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P) hr ?_ ?_
      · intro u hu v hv
        have hp : (δ : Ω) * u / β ∈ M := (hM _).2 ⟨u, hu, by field_simp⟩
        have hq : (δ' : Ω) * v / β' ∈ N := (hN _).2 ⟨v, hv, by field_simp⟩
        have hpq : ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') ∈ P := by
          refine InvertibleProductRep.mem_of_local B P hP _ fun m hm => ?_
          obtain ⟨i, ⟨-, hMz⟩, ⟨-, hNz⟩, ⟨⟨b'', hb'', hgh⟩, -⟩⟩ := hloc m hm
          obtain ⟨b, c, hb, e₁⟩ := hMz _ hp
          obtain ⟨b', c', hb', e₂⟩ := hNz _ hq
          refine ⟨b * b' * b'', notin m hm _ _ _ hb hb' hb'', ?_⟩
          have eq : ((b * b' * b'' : B) : Ω) * (((δ : Ω) * u / β) * ((δ' : Ω) * v / β')) =
              ((c * c' : B) : Ω) * ((b'' : Ω) * (g i * h i)) := by
            push_cast
            linear_combination ((b' : Ω) * b'' * ((δ' : Ω) * v / β')) * e₁ + ((c : Ω) * b'' * g i) * e₂
          rw [eq]
          exact hP _ (c * c').2 _ hgh
        have : ((δ * δ' : B) : Ω) * ((u * v : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') := by
          push_cast
          field_simp
        rw [this]
        exact hpq
      · intro a c ha hc
        have : ((δ * δ' : B) : Ω) * ((a + c : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ * δ' : B) : Ω) * (a : Ω) / ((β * β' : B) : Ω) +
              ((δ * δ' : B) : Ω) * (c : Ω) / ((β * β' : B) : Ω) := by
          push_cast
          ring
        rw [this]
        exact P.add_mem ha hc
    have hx : x = ((δ * δ' : B) : Ω) * (y : Ω) / ((β * β' : B) : Ω) := by
      rw [eq_div_iff hne]
      push_cast at e ⊢
      linear_combination e
    rw [hx]
    exact claim y hy

end GroundTheory.Heights₂.Heights.Targets
