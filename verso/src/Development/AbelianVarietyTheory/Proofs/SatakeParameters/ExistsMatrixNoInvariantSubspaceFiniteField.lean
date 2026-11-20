import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory

/- English proof (translation)
Introduce `κ _ _ a ha`. Take `⟨p, hp⟩` from `CharP.exists κ`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩`. Use `haveI : NeZero a := ⟨by omega⟩`. Set `L` to `FiniteField.Extension κ p a`.

Set `b : Module.Basis (Fin a) κ L` to `Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)`. Take `⟨g, hg⟩` from `IsCyclic.exists_monoid_generator (α := Lˣ)`. Set `β : L` to `(g : L)`. Use `⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩` and prove the remaining obligations. Set `e` to `b.equivFun`.

Establish `key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x)`. Introduce `x`. Simplify `LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x` using `[e, Module.Basis.equivFun_apply]`. Establish `stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W` using `fun x hx => key x ▸ hW _ hx`. Establish `stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ n ih`.

Introduce `x hx`. Use `stepβ _ (ih x hx)` as an intermediate fact. Simplify `this` using `[pow_succ', mul_assoc]`. Establish `stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W`. Introduce `y x hx`.

Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using `using W.zero_mem`. Take `⟨n, hn⟩` from `Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))`. Establish `: β ^ n = y`.

Use `congrArg (fun u : Lˣ => (u : L)) hn` as an intermediate fact. Simplify `this` using `[β]`. Rewrite using `[← this]`. Conclude with `stepPow n x hx`. Distinguish the cases in `h : W = ⊥`.

Conclude with `Or.inl h`. Use `right`. Take `⟨v, hvW, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Establish `hx0 : e.symm v ≠ 0`. Introduce `h0`.

Apply `hv0` to reduce the goal to its premises. Simplify using `using congrArg e h0`. Establish `hxW : e (e.symm v) ∈ W` using `by simpa using hvW`. Rewrite using `[eq_top_iff]`. Introduce `u _`.

Use `stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW` as an intermediate fact. Rewrite `this` using `[mul_assoc, inv_mul_cancel₀ hx0, mul_one]`. Simplify using `using this`.
-/
theorem exists_matrix_no_invariant_subspace :
    ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ,
      ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro κ _ _ a ha
  obtain ⟨p, hp⟩ := CharP.exists κ
  haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  haveI : NeZero a := ⟨by omega⟩
  let L := FiniteField.Extension κ p a
  let b : Module.Basis (Fin a) κ L :=
    Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  let β : L := (g : L)
  refine ⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩

  let e := b.equivFun
  have key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x) := by
    intro x
    simpa [e, Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x

  have stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W := fun x hx => key x ▸ hW _ hx
  have stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := stepβ _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W := by
    intro y x hx
    by_cases hy : y = 0
    · subst hy; simpa using W.zero_mem
    · obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))
      have : β ^ n = y := by
        have := congrArg (fun u : Lˣ => (u : L)) hn
        simpa [β] using this
      rw [← this]; exact stepPow n x hx
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hx0 : e.symm v ≠ 0 := by
      intro h0; apply hv0; simpa using congrArg e h0
    have hxW : e (e.symm v) ∈ W := by simpa using hvW
    rw [eq_top_iff]
    intro u _
    have := stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    simpa using this

end GlobalTheory
