import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

open Module

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Use `haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite`. Proceed by induction on `m with`. Consider the case `zero`. Conclude with `⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩`. Consider the case `succ m ih`.

Take `⟨v, hv, hs⟩` from `ih (Nat.le_of_succ_le hm)`. Use `set U := Submodule.span (ZMod l) (Set.range v) with hU`. Establish `hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U` using `fun j => Submodule.span_mono (Set.image_subset_range _ _)`. Establish `hvU : ∀ j, v j ∈ U` using `fun j => Submodule.subset_span ⟨j, rfl⟩`. Establish `hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U`.

Introduce `h u hu`. Establish `hle : U ≤ U.comap (ρ h)`. Rewrite using `[hU, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h1` using `hmono j (hs h j)`.

Establish `h2` using `U.add_mem h1 (hvU j)`. Simplify using `using h2`. Conclude with `hle hu`. Establish `hne : U ≠ ⊤`. Introduce `htop`.

Establish `h1 : finrank (ZMod l) U = m`. Rewrite using `[hU, finrank_span_eq_card hv]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[htop, finrank_top]`. Use linear arithmetic over natural numbers and integers.

Take `⟨x, hx, hxs⟩` from `hF l H hH V ρ U hst hne`. Use `⟨Fin.snoc v x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(linearIndependent_fin_snoc).2 ⟨hv, hx⟩`. Introduce `h j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations.

Establish `himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`. Establish `hi' : i ≠ Fin.last m` using `ne_of_lt hi`.

Take `⟨i', rfl⟩` from `Fin.exists_castSucc_eq.2 hi'`. Conclude with `⟨i', by simp⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩`. Simplify using `only [Fin.snoc_last]`.

Rewrite using `[himg]`. Conclude with `hxs h`. Establish `himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc}`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `⟨i.castSucc, by simpa using hi, by simp⟩`.

Simplify using `only [Fin.snoc_castSucc]`. Conclude with `Submodule.span_mono himg (hs h j)`.
-/
private theorem exists_invariant_flag_mod_l (hF : FixVec) (l : ℕ) [Fact l.Prime] (H : Type) [Group H] (hH : IsPGroup l H)
    (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V] (ρ : Representation (ZMod l) H V)
    (m : ℕ) (hm : m ≤ finrank (ZMod l) V) :
    ∃ v : Fin m → V, LinearIndependent (ZMod l) v ∧
      ∀ h j, ρ h (v j) - v j ∈ Submodule.span (ZMod l) (v '' {i | i < j}) := by
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hs⟩ := ih (Nat.le_of_succ_le hm)
    set U := Submodule.span (ZMod l) (Set.range v) with hU
    have hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U := fun j =>
      Submodule.span_mono (Set.image_subset_range _ _)
    have hvU : ∀ j, v j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
      intro h u hu
      have hle : U ≤ U.comap (ρ h) := by
        rw [hU, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have h1 := hmono j (hs h j)
        have h2 := U.add_mem h1 (hvU j)
        simpa using h2
      exact hle hu
    have hne : U ≠ ⊤ := by
      intro htop
      have h1 : finrank (ZMod l) U = m := by
        rw [hU, finrank_span_eq_card hv]; simp
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨x, hx, hxs⟩ := hF l H hH V ρ U hst hne
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · exact (linearIndependent_fin_snoc).2 ⟨hv, hx⟩
    · intro h j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · have himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v := by
          ext y
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hi' : i ≠ Fin.last m := ne_of_lt hi
            obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi'
            exact ⟨i', by simp⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
        simp only [Fin.snoc_last]
        rw [himg]
        exact hxs h
      · have himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc} := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i.castSucc, by simpa using hi, by simp⟩
        simp only [Fin.snoc_castSucc]
        exact Submodule.span_mono himg (hs h j)

/- English proof (translation)
Introduce `hF l _ H _ hH V _ _ _ ρ`. Use `haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite`. Take `⟨v, hv, hs⟩` from `exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl`. Establish `hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v)` using `(hv.span_eq_top_of_card_eq_finrank' (by simp)).ge`. Set `b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V` to `Basis.mk hv hsp`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Introduce `h i j hji`. Establish `hb : ∀ j, b j = v j` using `fun j => Basis.mk_apply hv hsp j`. Establish `hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j})`. Establish `: (b : _ → V) '' {i | i < j} = v '' {i | i < j}`.

Use extensionality with `y`. Simplify using `[hb]`. Rewrite using `[this, hb]`. Conclude with `hs h j`. Establish `hsupp` using `(Basis.mem_span_image b).1 hmem`.

Assume the negation of the conclusion as `hne`. Establish `hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _)`. Simplify using `using hne`. Use `hsupp hi` as an intermediate fact. Conclude with `absurd this (not_lt.2 hji)`.
-/
theorem flag_pf : FixVec → Flag := by
  intro hF l _ H _ hH V _ _ _ ρ
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  obtain ⟨v, hv, hs⟩ := exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (by simp)).ge
  let b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V := Basis.mk hv hsp
  refine ⟨b, ?_⟩
  intro h i j hji
  have hb : ∀ j, b j = v j := fun j => Basis.mk_apply hv hsp j
  have hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j}) := by
    have : (b : _ → V) '' {i | i < j} = v '' {i | i < j} := by
      ext y; simp [hb]
    rw [this, hb]
    exact hs h j
  have hsupp := (Basis.mem_span_image b).1 hmem
  by_contra hne
  have hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _) := by
    simpa using hne
  have := hsupp hi
  exact absurd this (not_lt.2 hji)

end UpperTheory.Gal.Gen
