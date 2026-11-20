import Mathlib

open CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Set `g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type)` to `fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)`. Set `F : ℕᵒᵖ ⥤ Type` to `Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g`. Use `haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype`. Use `haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype`. Take `⟨u, hu⟩` from `nonempty_sections_of_finite_inverse_system F`.

Use `⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hu (homOfLE (Nat.le_add_right n 1)).op`. Establish `hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n` using `Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n`. Rewrite `h` using `[hm]`. Conclude with `congrArg Subtype.val h`.
-/
theorem exists_compatible_seq_of_finite_nonempty
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  classical
  let g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type) :=
    fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  have hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n
  rw [hm] at h
  exact congrArg Subtype.val h

end GlobalTheory
