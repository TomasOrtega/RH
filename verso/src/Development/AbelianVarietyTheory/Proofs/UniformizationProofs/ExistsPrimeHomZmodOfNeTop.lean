import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤`. Introduce `h'`. Apply `h` to reduce the goal to its premises. Use extensionality with `x`. Establish `: x ∈ AddSubgroup.toIntSubmodule Λ` using `by rw [h']; trivial`.

Conclude with `⟨fun _ => trivial, fun _ => this⟩`. Take `⟨M, hM, hle⟩` from `(eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1`. Establish `hs : IsSimpleModule ℤ (X ⧸ M)` using `isSimpleModule_iff_isCoatom.mpr hM`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Take `⟨n, hn⟩` from `(IsPrincipalIdealRing.principal I).principal`.

Establish `hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)}`. Rewrite using `[Int.span_natAbs]`. Conclude with `hn`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`.

Establish `hb : I = ⊥` using `by simpa using hn`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb`. Establish `hp : (n.natAbs).Prime`. Use `hI.isPrime` as an intermediate fact. Rewrite `this` using `[hn']`.

Establish `h2` using `(Ideal.span_singleton_prime (by simpa using hn0)).mp this`. Conclude with `Nat.prime_iff_prime_int.mpr h2`. Set `g : (ℤ ⧸ I) ≃+* ZMod n.natAbs` to `(Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)`. Use `⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hM.1` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : g (e (M.mkQ x)) = 0` using `DFunLike.congr_fun h0 x`. Rewrite `hx` using `[map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective]`.

Conclude with `(Submodule.Quotient.mk_eq_zero M).mp hx`. Introduce `x hx`. Establish `: M.mkQ x = 0` using `(Submodule.Quotient.mk_eq_zero M).mpr (hle hx)`. Express the relevant statement in the definitionally equal form `g (e (M.mkQ x)) = 0`. Rewrite using `[this, map_zero, map_zero]`.
-/
theorem exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]

/- English proof (translation)
Introduce `X _ _ S S₂ ⟨a, ha⟩ h hd`. Establish `h02 : (0 : X) ∈ S₂` using `by simpa using ((h a a).mp ⟨ha, ha⟩).2`. Establish `h0 : (0 : X) ∈ S` using `((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1`. Establish `heq : S₂ = S`. Use extensionality with `x`.

Use `h x 0` as an intermediate fact. Simplify using `only [add_zero, sub_zero, and_self, h0, and_true] at this`. Conclude with `this.symm`. Substitute `heq` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations.

Set `Λ : AddSubgroup X` to `{ carrier := S₂ zero_mem' := h0 add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1 neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }`. Use `⟨Λ, rfl, ?_⟩` and prove the remaining obligations. Distinguish the cases in `ht : Λ = ⊤`. Conclude with `Or.inl ht`. Use `right`.

Take `⟨l, hl, f, hf, hΛ⟩` from `exists_prime_hom_zmod_of_ne_top X Λ ht`. Use `⟨l, hl, ?_, f, hf, hΛ⟩` and prove the remaining obligations. Use `hl.odd_of_ne_two ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hf` to reduce the goal to its premises.

Use extensionality with `x`. Take `⟨z, hz⟩` from `hd x`. Establish `h1` using `hΛ _ hz`. Establish `h2 : f z + f z = 0` using `CharTwo.add_self_eq_zero _`. Rewrite `h1` using `[map_add, map_add, h2, add_zero]`.

Simplify using `using h1`.
-/
theorem support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by
  intro X _ _ S S₂ ⟨a, ha⟩ h hd
  have h02 : (0 : X) ∈ S₂ := by simpa using ((h a a).mp ⟨ha, ha⟩).2
  have h0 : (0 : X) ∈ S := ((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1
  have heq : S₂ = S := by
    ext x
    have := h x 0
    simp only [add_zero, sub_zero, and_self, h0, and_true] at this
    exact this.symm
  subst heq
  refine ⟨rfl, ?_⟩
  let Λ : AddSubgroup X :=
    { carrier := S₂
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1
      neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }
  refine ⟨Λ, rfl, ?_⟩
  by_cases ht : Λ = ⊤
  · exact Or.inl ht
  · right
    obtain ⟨l, hl, f, hf, hΛ⟩ := exists_prime_hom_zmod_of_ne_top X Λ ht
    refine ⟨l, hl, ?_, f, hf, hΛ⟩
    refine hl.odd_of_ne_two ?_
    rintro rfl
    apply hf
    ext x
    obtain ⟨z, hz⟩ := hd x
    have h1 := hΛ _ hz
    have h2 : f z + f z = 0 := CharTwo.add_self_eq_zero _
    rw [map_add, map_add, h2, add_zero] at h1
    simpa using h1

end GlobalTheory
